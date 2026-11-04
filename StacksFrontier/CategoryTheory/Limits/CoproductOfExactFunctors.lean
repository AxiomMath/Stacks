module

public import StacksFrontier.CategoryTheory.Limits.PiEval
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# A coproduct of exact functors is exact

Let `A : I → Type u'` be a family of categories and let `B` be a category with coproducts
indexed by `I`. A family of functors `F i : A i ⥤ B` has a *coproduct*
`CategoryTheory.Limits.sigmaOfFamily F : (∀ i, A i) ⥤ B`, sending a family of objects `X` to
`∐ i, (F i).obj (X i)`. This file proves that it is exact as soon as every `F i` is and
coproducts indexed by `I` are exact in `B` — Grothendieck's axiom AB4 for the shape
`Discrete I`.

The index type, the objects and morphisms of the `A i`, and the objects and morphisms of `B`
are in five independent universes.

## Main results

* `CategoryTheory.Limits.sigmaFunctorPreservesFiniteLimits`: the coproduct functor
  `Limits.Sigma.functor I : (I → B) ⥤ B` preserves finite limits when `B` satisfies AB4 for the
  shape `Discrete I`. This is only a repackaging of `HasExactColimitsOfShape`, which is phrased
  for `colim : (Discrete I ⥤ B) ⥤ B`.
* `CategoryTheory.Limits.sigmaOfFamilyAdjunction`: a coproduct of left adjoints,
  `(X i)_i ↦ ∐ i, (L i).obj (X i)`, is left adjoint to the family of the right adjoints,
  `M ↦ ((R i).obj M)_i`.
* `CategoryTheory.Limits.exactFunctor_sigmaOfFamily`: **a coproduct of exact functors is
  exact.**

## Implementation notes

The functor is built as a composite rather than by hand, which is what makes both halves of
exactness formal:

`sigmaOfFamily F = Functor.pi' (fun i => Pi.eval A i ⋙ F i) ⋙ Limits.Sigma.functor I`.

Evaluation at a component preserves all limits and colimits that exist componentwise
(`CategoryTheory.Pi.evalPreservesLimitsOfShape`), a functor into a product of categories
preserves whatever each of its components preserves (`CategoryTheory.Pi.pi'PreservesLimit`), and
`Limits.Sigma.functor I` is `colim` up to the equivalence `(I → B) ≌ (Discrete I ⥤ B)`, so it
preserves all colimits — `colim` is a left adjoint — and preserves finite limits exactly when
AB4 holds.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe w v u v' u'

section SigmaFunctor

variable (I : Type w) {B : Type u} [Category.{v} B] [HasCoproductsOfShape I B]

/-- The coproduct functor `(I → B) ⥤ B` preserves finite colimits: it is `colim` up to the
equivalence `(I → B) ≌ (Discrete I ⥤ B)`, and `colim` is a left adjoint. -/
instance sigmaFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (Sigma.functor (C := B) I) := by
  have : PreservesColimitsOfSize.{0, 0} (colim (J := Discrete I) (C := B)) :=
    (colimConstAdj (J := Discrete I) (C := B)).leftAdjoint_preservesColimits
  exact preservesFiniteColimits_of_natIso (piEquivalenceFunctorDiscreteCompColim I)

/-- If coproducts indexed by `I` are exact in `B`, the coproduct functor `(I → B) ⥤ B` preserves
finite limits: this is `HasExactColimitsOfShape` stated for the coproduct functor rather than for
`colim : (Discrete I ⥤ B) ⥤ B`. -/
instance sigmaFunctorPreservesFiniteLimits [HasExactColimitsOfShape (Discrete I) B] :
    PreservesFiniteLimits (Sigma.functor (C := B) I) :=
  preservesFiniteLimits_of_natIso (piEquivalenceFunctorDiscreteCompColim I)

/-- **The coproduct functor `(I → B) ⥤ B` is left adjoint to the diagonal.** It is `colim` up to
the equivalence `(I → B) ≌ (Discrete I ⥤ B)`, and `colim` is left adjoint to the constant
functor. -/
noncomputable def sigmaFunctorAdjunction :
    Sigma.functor (C := B) I ⊣ Functor.pi' (fun _ : I => 𝟭 B) :=
  (piEquivalenceFunctorDiscrete I B).toAdjunction.comp
    (colimConstAdj (J := Discrete I) (C := B))

end SigmaFunctor

section Coproduct

variable {I : Type w} {A : I → Type u'} [∀ i, Category.{v'} (A i)]
  {B : Type u} [Category.{v} B] [HasCoproductsOfShape I B]

/-- The coproduct of a family of functors `F i : A i ⥤ B`: it sends a family of objects `X` to
`∐ i, (F i).obj (X i)`. -/
noncomputable def sigmaOfFamily (F : ∀ i, A i ⥤ B) : (∀ i, A i) ⥤ B :=
  Functor.pi' (C := fun _ : I => B) (fun i => Pi.eval A i ⋙ F i) ⋙ Sigma.functor I

variable (F : ∀ i, A i ⥤ B)

/-- `sigmaOfFamily F` sends a family of objects `X` to `∐ i, (F i).obj (X i)`. -/
@[simp]
lemma sigmaOfFamily_obj (X : ∀ i, A i) :
    (sigmaOfFamily F).obj X = ∐ fun i => (F i).obj (X i) :=
  rfl

/-- `sigmaOfFamily F` sends a family of morphisms `f` to `Sigma.map fun i => (F i).map (f i)`. -/
@[simp]
lemma sigmaOfFamily_map {X Y : ∀ i, A i} (f : X ⟶ Y) :
    (sigmaOfFamily F).map f = Sigma.map fun i => (F i).map (f i) :=
  rfl

/-- **A coproduct of left adjoints is left adjoint to the family of the right adjoints**:
`(X i)_i ↦ ∐ i, (L i).obj (X i)` is left adjoint to `M ↦ ((R i).obj M)_i`. -/
noncomputable def sigmaOfFamilyAdjunction {L : ∀ i, A i ⥤ B} {R : ∀ i, B ⥤ A i}
    (adj : ∀ i, L i ⊣ R i) : sigmaOfFamily L ⊣ Functor.pi' R :=
  (Functor.piAdjunction adj).comp (sigmaFunctorAdjunction I)

/-- A coproduct of functors preserving finite colimits preserves finite colimits. -/
instance sigmaOfFamilyPreservesFiniteColimits [∀ i, HasFiniteColimits (A i)]
    [∀ i, PreservesFiniteColimits (F i)] : PreservesFiniteColimits (sigmaOfFamily F) := by
  have : PreservesFiniteColimits (Functor.pi' (C := fun _ : I => B)
      (fun i => Pi.eval A i ⋙ F i)) := ⟨fun _ _ _ => inferInstance⟩
  exact inferInstanceAs (PreservesFiniteColimits (_ ⋙ Sigma.functor I))

/-- A coproduct of functors preserving finite limits preserves finite limits, provided
coproducts indexed by `I` are exact in `B`. -/
instance sigmaOfFamilyPreservesFiniteLimits [∀ i, HasFiniteLimits (A i)]
    [∀ i, PreservesFiniteLimits (F i)] [HasExactColimitsOfShape (Discrete I) B] :
    PreservesFiniteLimits (sigmaOfFamily F) := by
  have : PreservesFiniteLimits (Functor.pi' (C := fun _ : I => B)
      (fun i => Pi.eval A i ⋙ F i)) := ⟨fun _ _ _ => inferInstance⟩
  exact inferInstanceAs (PreservesFiniteLimits (_ ⋙ Sigma.functor I))

/-- **A coproduct of exact functors is exact**, provided coproducts indexed by `I` are exact in
the target — Grothendieck's axiom AB4 for the shape `Discrete I`. -/
theorem exactFunctor_sigmaOfFamily [∀ i, HasFiniteLimits (A i)] [∀ i, HasFiniteColimits (A i)]
    [HasExactColimitsOfShape (Discrete I) B] (hF : ∀ i, exactFunctor (A i) B (F i)) :
    exactFunctor (∀ i, A i) B (sigmaOfFamily F) := by
  have h₁ : ∀ i, PreservesFiniteLimits (F i) := fun i => ((exactFunctor_iff _).mp (hF i)).1
  have h₂ : ∀ i, PreservesFiniteColimits (F i) := fun i => ((exactFunctor_iff _).mp (hF i)).2
  exact (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

end Coproduct

end CategoryTheory.Limits

end
