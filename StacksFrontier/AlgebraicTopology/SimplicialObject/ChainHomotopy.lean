module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic

/-!
# Simplicial homotopies induce chain homotopies of Moore complexes

A homotopy between morphisms of simplicial objects in an abelian category induces a chain homotopy
between the induced morphisms of (normalized) Moore complexes.
-/

/-!
## The chain homotopy induced by a simplicial homotopy

Let `A` be a preadditive category, let `U`, `V` be simplicial objects of `A` and let `a, b : U ⟶ V`
be morphisms. A homotopy from `a` to `b` is a morphism `h : U × Δ[1] ⟶ V` with `e₀ ≫ h = a` and
`e₁ ≫ h = b` ([Stacks, Tag 019K], `CategoryTheory.SimplicialObject.IsHomotopy`), and by
[Stacks, Tag 019L] it is the same thing as a family of morphisms `h_{n,i} : Uₙ ⟶ Vₙ`, for `n ≥ 0`
and `0 ≤ i ≤ n + 1`, satisfying the relations `CategoryTheory.SimplicialObject.HtpyRel a b`; in
particular `h_{n,0} = bₙ` and `h_{n,n+1} = aₙ`. Out of such a family [Stacks, Section 019Q]
builds a homotopy of chain complexes between the two induced maps `s(a), s(b) : s(U) ⟶ s(V)` of
Moore complexes, whose degree-`n` component `s(h)ₙ : Uₙ ⟶ V_{n+1}` is the alternating sum

`s(h)ₙ = ∑_{i=0}^{n} (-1)^{i+1} h_{n+1,i+1} ∘ sⁿᵢ`

of [Stacks, Equation 019R]. That the resulting family is a chain homotopy, i.e. satisfies
`d_{n+1} ∘ s(h)ₙ + s(h)_{n-1} ∘ dₙ = aₙ - bₙ`, is [Stacks, Tag 019S].

Mathlib's `CategoryTheory.SimplicialObject.Homotopy a b` records instead the composites appearing
in the displayed sum, `Homotopy.h i : Uₙ ⟶ V_{n+1}` for `i : Fin (n + 1)`, and its
`Homotopy.toChainHomotopy` is a chain homotopy between `s(a)` and `s(b)`. The bridge
`HtpyRel.toHomotopy` turns a family satisfying the relations of [Stacks, Tag 019L] into the
Mathlib homotopy whose `i`-th component in degree `n` is `h_{n+1,i+1} ∘ sⁿᵢ`, and the chain
homotopy `s(h)` of the source is the `toChainHomotopy` of that homotopy: its degree-`n`
component is the displayed sum, literally, and its components in the other bidegrees vanish
(`Homotopy.ToChainHomotopy.hom_eq_zero`).

### Main definitions

* `CategoryTheory.SimplicialObject.HtpyRel.toHomotopy`: the Mathlib simplicial homotopy from `a`
  to `b` with components `h_{n+1,i+1} ∘ sⁿᵢ`, out of a family `h_{n,i}` satisfying the relations
  of [Stacks, Tag 019L].

### Main results

* `CategoryTheory.SimplicialObject.HtpyRel.toChainHomotopy_hom_eq`: the degree-`n` component of
  the chain homotopy `s(h)` induced by a family `h_{n,i}` satisfying the relations of
  [Stacks, Tag 019L] is `∑_{i=0}^{n} (-1)^{i+1} h_{n+1,i+1} ∘ sⁿᵢ`.
* `CategoryTheory.SimplicialObject.IsHomotopy.toChainHomotopy_hom_eq`: the same for a homotopy
  `h : U × Δ[1] ⟶ V` in the sense of [Stacks, Tag 019K], with `h_{n,i}` its components
  `homotopyComponent h n i`.

### References

* [Stacks, Tag 019R](https://stacks.math.columbia.edu/tag/019R)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SSet

open scoped Simplicial

universe w v u

namespace CategoryTheory.SimplicialObject.HtpyRel

variable {C : Type u} [Category.{v} C] {U V : SimplicialObject C} {a b : U ⟶ V}
  {hc : ∀ (n : ℕ), Fin (n + 2) →
    (U.obj (op (SimplexCategory.mk n)) ⟶ V.obj (op (SimplexCategory.mk n)))}

/-- Relation 2 of [Stacks, Tag 019L], with the index of the right-hand component given by its
value. -/
private lemma face_gt' (hrel : HtpyRel a b hc) (n : ℕ) (j : Fin (n + 2)) (i : Fin (n + 3))
    (k : Fin (n + 2)) (hij : j.castSucc < i) (hk : (k : ℕ) + 1 = i) :
    hc (n + 1) i ≫ V.δ j = U.δ j ≫ hc n k :=
  (hrel.face_gt n j i hij).trans (congrArg (U.δ j ≫ hc n ·) (Fin.ext (by simp; omega)))

/-- Relation 3 of [Stacks, Tag 019L], with the index of the right-hand component given by its
value. -/
private lemma face_le' (hrel : HtpyRel a b hc) (n : ℕ) (j : Fin (n + 2)) (i : Fin (n + 3))
    (k : Fin (n + 2)) (hij : i ≤ j.castSucc) (hk : (k : ℕ) = i) :
    hc (n + 1) i ≫ V.δ j = U.δ j ≫ hc n k :=
  (hrel.face_le n j i hij).trans (congrArg (U.δ j ≫ hc n ·) (Fin.ext (by simp; omega)))

/-- Relation 4 of [Stacks, Tag 019L], with the index of the right-hand component given by its
value. -/
private lemma degen_gt' (hrel : HtpyRel a b hc) (n : ℕ) (j : Fin (n + 1)) (i : Fin (n + 2))
    (k : Fin (n + 3)) (hji : j.castSucc < i) (hk : (k : ℕ) = i + 1) :
    hc n i ≫ V.σ j = U.σ j ≫ hc (n + 1) k :=
  (hrel.degen_gt n j i hji).trans (congrArg (U.σ j ≫ hc (n + 1) ·) (Fin.ext (by simp; omega)))

/-- Relation 5 of [Stacks, Tag 019L], with the index of the right-hand component given by its
value. -/
private lemma degen_le' (hrel : HtpyRel a b hc) (n : ℕ) (j : Fin (n + 1)) (i : Fin (n + 2))
    (k : Fin (n + 3)) (hij : i ≤ j.castSucc) (hk : (k : ℕ) = i) :
    hc n i ≫ V.σ j = U.σ j ≫ hc (n + 1) k :=
  (hrel.degen_le n j i hij).trans (congrArg (U.σ j ≫ hc (n + 1) ·) (Fin.ext (by simp; omega)))

/-- The Mathlib simplicial homotopy from `a` to `b` attached to a family `h_{n,i} : Uₙ ⟶ Vₙ`
satisfying the relations of [Stacks, Tag 019L]: its `i`-th component in degree `n`, for
`0 ≤ i ≤ n`, is the composite `h_{n+1,i+1} ∘ sⁿᵢ : Uₙ ⟶ V_{n+1}` of the footnote to
[Stacks, Tag 019M]. -/
noncomputable def toHomotopy (hrel : HtpyRel a b hc) : Homotopy a b where
  h i := U.σ i ≫ hc _ i.succ.castSucc
  h_zero_comp_δ_zero n := by
    rw [Category.assoc, hrel.face_gt' n 0 _ 0 (by simp) (by simp),
      ← Category.assoc, U.δ_comp_σ_self' (by simp), Category.id_comp, hrel.bdry₀]
  h_last_comp_δ_last n := by
    rw [Category.assoc, hrel.face_le' n (Fin.last (n + 1)) _ (Fin.last (n + 1))
      (by simp) (by simp), ← Category.assoc,
      U.δ_comp_σ_succ' (Fin.succ_last n).symm, Category.id_comp, hrel.bdry₁]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    rw [Category.assoc, hrel.face_gt' _ i.castSucc _ j.succ.castSucc
      (by simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc,
        Fin.val_succ] at hij ⊢; omega) (by simp), ← Category.assoc,
      U.δ_comp_σ_of_le hij, Category.assoc]
  h_succ_comp_δ_castSucc_succ j := by
    rw [Category.assoc, Category.assoc,
      hrel.face_gt' _ j.castSucc.succ _ j.succ.castSucc (by simp [Fin.lt_def]) (by simp),
      hrel.face_le' _ j.castSucc.succ _ j.succ.castSucc (by simp) (by simp),
      ← Category.assoc, ← Category.assoc, U.δ_comp_σ_self' (Fin.ext (by simp)),
      U.δ_comp_σ_succ]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    rw [Category.assoc, hrel.face_le' _ i.succ _ j.succ.castSucc
      (by simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc,
        Fin.val_succ] at hji ⊢; omega) (by simp), ← Category.assoc,
      U.δ_comp_σ_of_gt hji, Category.assoc]
  h_comp_σ_castSucc_of_le i j hij := by
    rw [Category.assoc, hrel.degen_gt' _ i.castSucc _ j.succ.succ.castSucc
      (by simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc,
        Fin.val_succ] at hij ⊢; omega) (by simp), ← Category.assoc,
      U.σ_comp_σ hij, Category.assoc]
  h_comp_σ_succ_of_lt i j hji := by
    rw [Category.assoc, hrel.degen_le' _ i.succ _ j.castSucc.succ.castSucc
      (by simp only [Fin.le_def, Fin.val_castSucc,
        Fin.val_succ] at hji ⊢; omega) (by simp), ← Category.assoc,
      ← U.σ_comp_σ hji, Category.assoc]

variable [Preadditive C]

/-- **The chain homotopy induced by a simplicial homotopy.** Let `h_{n,i} : Uₙ ⟶ Vₙ` be a family
satisfying the relations of [Stacks, Tag 019L] relative to `a, b : U ⟶ V`, that is, a homotopy
from `a` to `b` in the form of [Stacks, Tag 019M]. Then the degree-`n` component
`s(h)ₙ : Uₙ ⟶ V_{n+1}` of the induced chain homotopy between `s(a)` and `s(b)` is
`∑_{i=0}^{n} (-1)^{i+1} h_{n+1,i+1} ∘ sⁿᵢ`. -/
@[stacks 019R "the chain homotopy `s(h)` is `toChainHomotopy` of the bridge \
  `HtpyRel.toHomotopy` to Mathlib's `SimplicialObject.Homotopy`, a chain homotopy between \
  `s(a)` and `s(b)` (019S); stated is its degree-`n` component, in the source's form, for the \
  family `h_{n,i}` of 019L; the components in the other bidegrees are zero by Mathlib's \
  `Homotopy.ToChainHomotopy.hom_eq_zero`"]
theorem toChainHomotopy_hom_eq (hrel : HtpyRel a b hc) (n : ℕ) :
    hrel.toHomotopy.toChainHomotopy.hom n (n + 1) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) • (U.σ i ≫ hc (n + 1) i.succ.castSucc) := by
  change Homotopy.ToChainHomotopy.hom hrel.toHomotopy n (n + 1) = _
  rw [Homotopy.ToChainHomotopy.hom_eq, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ, mul_neg_one, neg_smul]
  rfl

end CategoryTheory.SimplicialObject.HtpyRel

namespace CategoryTheory.SimplicialObject.IsHomotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {U V : SimplicialObject C} {a b : U ⟶ V}
  [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{w}).obj m => U.obj m]

/-- **The chain homotopy induced by a homotopy `U × Δ[1] ⟶ V`.** Let `h : U × Δ[1] ⟶ V` be a
homotopy from `a` to `b` in the sense of [Stacks, Tag 019K], with components
`h_{n,i} = homotopyComponent h n i : Uₙ ⟶ Vₙ`. Then the degree-`n` component
`s(h)ₙ : Uₙ ⟶ V_{n+1}` of the induced chain homotopy between `s(a)` and `s(b)` is
`∑_{i=0}^{n} (-1)^{i+1} h_{n+1,i+1} ∘ sⁿᵢ`. -/
@[stacks 019R "the homotopy is the morphism `h : U × Δ[1] ⟶ V` of 019K, as in the source's \
  section 019Q, and `h_{n,i}` is `homotopyComponent h n i`; the chain homotopy `s(h)` is \
  `toChainHomotopy` of the Mathlib homotopy `(htpy_forward a b h hh).toHomotopy` built from \
  these components through 019L"]
theorem toChainHomotopy_hom_eq {h : U.copower Δ[1] ⟶ V} (hh : IsHomotopy h a b) (n : ℕ) :
    (htpy_forward a b h hh).toHomotopy.toChainHomotopy.hom n (n + 1) =
      ∑ i : Fin (n + 1),
        ((-1 : ℤ) ^ ((i : ℕ) + 1)) • (U.σ i ≫ homotopyComponent h (n + 1) i.succ.castSucc) :=
  (htpy_forward a b h hh).toChainHomotopy_hom_eq n

end CategoryTheory.SimplicialObject.IsHomotopy

end

end

/-!
## Homotopies of simplicial objects and the Moore complexes

Let `A` be an additive category and `U`, `V` simplicial objects of `A`. A *homotopy* from
`a : U ⟶ V` to `b : U ⟶ V` is a family of morphisms `h_{n, i} : Uₙ ⟶ Vₙ` satisfying the
relations of [Stacks, Tag 019L], and `a` and `b` are *homotopic* when they are related by a
finite chain of morphisms two consecutive members of which always admit a homotopy in one
direction or the other — that is, by the equivalence relation generated by "there is a homotopy
from `a` to `b`" ([Stacks, Tag 019K] (2), [Stacks, Tag 019M]). A morphism `a : U ⟶ V` is a
*homotopy equivalence* when there is `b : V ⟶ U` with `a ≫ b` homotopic to `𝟙 U` and `b ≫ a`
homotopic to `𝟙 V` ([Stacks, Tag 019N]).

Write `s = alternatingFaceMapComplex A` for the Moore complex and, when `A` is abelian,
`N = normalizedMooreComplex A` for the normalized Moore complex ([Stacks, Tag 0194]). Homotopic
morphisms have chain homotopic images under both functors ([Stacks, Tag 019S]), and the image
of a homotopy equivalence under either functor is a homotopy equivalence of chain complexes in
the sense of [Stacks, Tag 010X] ([Stacks, Tag 019T]).

### Main results

* `AlgebraicTopology.homotopic_normalizedMooreComplex_map`: homotopic morphisms `a, b : U ⟶ V`
  of simplicial objects of an abelian category have chain homotopic images
  `N(a), N(b) : N(U) ⟶ N(V)`.
* `AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map`: the Moore complex
  `s(a) : s(U) ⟶ s(V)` of a homotopy equivalence `a : U ⟶ V` of simplicial objects of a
  preadditive category is a homotopy equivalence of chain complexes.
* `AlgebraicTopology.homotopyEquivalences_normalizedMooreComplex_map`: over an abelian
  category, the normalized Moore complex `N(a) : N(U) ⟶ N(V)` of a homotopy equivalence
  `a : U ⟶ V` is a homotopy equivalence of chain complexes.

### Implementation notes

Being homotopic is spelled `Relation.EqvGen fun a b => Nonempty (Homotopy a b)`, as in
[Stacks, Tag 019W] and in the definition of `CategoryTheory.SimplicialObject.homotopyEquivalences`
([Stacks, Tag 019N]): the source's chain `a = a₀, …, aₙ = b` is the description of
`Relation.EqvGen` as the smallest equivalence relation containing a given relation, and
`Homotopy` is Mathlib's `CategoryTheory.SimplicialObject.Homotopy`, whose datum
`h.h i : Uₙ ⟶ V_{n + 1}` is the composite `h_{n + 1, i + 1} ∘ sⁿᵢ` of the footnote to
[Stacks, Tag 019M].

Being chain homotopic is Mathlib's `homotopic A (ComplexShape.down ℕ)`, the relation whose
quotient is the homotopy category, and being a homotopy equivalence of chain complexes is the
morphism property `HomologicalComplex.homotopyEquivalences`, which pins the map rather than
merely relating the two complexes; by
`HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences` the latter says that the map
becomes an isomorphism in the homotopy category, so the three results also say that `s` and `N`
descend to homotopy categories.

### References

* [Stacks, Tag 019S]
* [Stacks, Tag 019T]
-/

section

section

universe v u

open CategoryTheory CategoryTheory.SimplicialObject AlgebraicTopology

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A]

section Preadditive

variable [Preadditive A] {U V : SimplicialObject A}

/-- If `a, b : U ⟶ V` are homotopic morphisms of simplicial objects of a preadditive category,
then `s(a), s(b) : s(U) ⟶ s(V)` are chain homotopic. -/
private theorem homotopic_alternatingFaceMapComplex_map {a b : U ⟶ V}
    (h : Relation.EqvGen (fun a b : U ⟶ V => Nonempty (Homotopy a b)) a b) :
    homotopic A (ComplexShape.down ℕ)
      ((alternatingFaceMapComplex A).map a) ((alternatingFaceMapComplex A).map b) :=
  ((homotopy_congruence A _).equivalence.comap (alternatingFaceMapComplex A).map).eqvGen_iff.mp
    (Relation.EqvGen.mono (fun _ _ h => h.map Homotopy.toChainHomotopy) _ _ h)

/-- If `a ≫ b : U ⟶ U` is homotopic to `𝟙 U`, then `s(a) ≫ s(b)` is chain homotopic to
`𝟙 s(U)`. -/
private theorem homotopic_alternatingFaceMapComplex_map_comp_id (a : U ⟶ V) (b : V ⟶ U)
    (h : Relation.EqvGen (fun f g : U ⟶ U => Nonempty (Homotopy f g)) (a ≫ b) (𝟙 U)) :
    homotopic A (ComplexShape.down ℕ)
      ((alternatingFaceMapComplex A).map a ≫ (alternatingFaceMapComplex A).map b)
      (𝟙 ((alternatingFaceMapComplex A).obj U)) := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    homotopic_alternatingFaceMapComplex_map h

end Preadditive

section Abelian

variable [Abelian A] {U V : SimplicialObject A}

/-- The canonical inclusion of the normalized complex is natural: it carries `N(a)` to
`s(a)`. -/
private theorem normalizedMooreComplex_map_comp_inclusionOfMooreComplexMap (a : U ⟶ V) :
    (normalizedMooreComplex A).map a ≫ inclusionOfMooreComplexMap V =
      inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a :=
  (inclusionOfMooreComplex A).naturality a

/-- The canonical inclusion `N(X) ⟶ s(X)` of the normalized complex is a homotopy equivalence
of chain complexes. -/
private theorem homotopyEquivalences_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)
      (inclusionOfMooreComplexMap X) :=
  ⟨DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex, rfl⟩

/-- The map `N(a)` of normalized complexes is the composite `N(U) → s(U) → s(V) → N(V)` of the
canonical inclusion, the map `s(a)` of Moore complexes and the canonical retraction. -/
private theorem normalizedMooreComplex_map_eq (a : U ⟶ V) :
    (normalizedMooreComplex A).map a = inclusionOfMooreComplexMap U ≫
      (alternatingFaceMapComplex A).map a ≫
        (DoldKan.splitMonoInclusionOfMooreComplexMap V).retraction := by
  rw [← Category.assoc, ← normalizedMooreComplex_map_comp_inclusionOfMooreComplexMap,
    Category.assoc, (DoldKan.splitMonoInclusionOfMooreComplexMap V).id, Category.comp_id]

variable {a b : U ⟶ V}

/-- **Homotopic morphisms have chain homotopic normalized Moore complexes.** If
`a, b : U ⟶ V` are homotopic morphisms of simplicial objects of an abelian category `A` —
related by a chain of morphisms consecutive members of which admit a simplicial homotopy in
one direction or the other — then the induced maps `N(a), N(b) : N(U) ⟶ N(V)` of normalized
Moore complexes are chain homotopic. -/
@[stacks 019S "the half about the Moore complex `s` is Mathlib's, so it gets no public name \
  here: a homotopy gives `SimplicialObject.Homotopy.toChainHomotopy`, and `homotopy_congruence` \
  propagates it along the source's chain; stated here is the half about `N`. `homotopic` is \
  Mathlib's chain homotopy relation, and being homotopic is spelled \
  `Relation.EqvGen fun a b => Nonempty (Homotopy a b)` as in 019W",
  sga "4½ Fonctions_L 1.4" "N preserves homotopy"]
public theorem homotopic_normalizedMooreComplex_map
    (h : Relation.EqvGen (fun a b : U ⟶ V => Nonempty (Homotopy a b)) a b) :
    homotopic A (ComplexShape.down ℕ)
      ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b) := by
  rw [normalizedMooreComplex_map_eq a, normalizedMooreComplex_map_eq b]
  exact (homotopic_alternatingFaceMapComplex_map h).map fun H => (H.compRight _).compLeft _

end Abelian

variable {U V : SimplicialObject A} {a : U ⟶ V}

/-- **The Moore complex of a homotopy equivalence of simplicial objects is a homotopy
equivalence of chain complexes.** Let `a : U ⟶ V` be a homotopy equivalence of simplicial
objects of a preadditive category `A`: there is `b : V ⟶ U` with `a ≫ b` homotopic to `𝟙 U`
and `b ≫ a` homotopic to `𝟙 V`, homotopic meaning related by the equivalence relation
generated by the existence of a simplicial homotopy ([Stacks, Tag 019N]). Then
`s(a) : s(U) ⟶ s(V)` is a homotopy equivalence of chain complexes. -/
@[stacks 019T "the first sentence, for the Moore complex `s`, with the source's `additive` \
  weakened to `Preadditive`, Mathlib's hypothesis for `alternatingFaceMapComplex`; the second \
  sentence is `homotopyEquivalences_normalizedMooreComplex_map` below. Being a homotopy \
  equivalence of chain complexes is `HomologicalComplex.homotopyEquivalences`, which pins the \
  map, and the hypothesis is 019N's `SimplicialObject.homotopyEquivalences`"]
public theorem homotopyEquivalences_alternatingFaceMapComplex_map [Preadditive A]
    (ha : SimplicialObject.homotopyEquivalences A a) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)
      ((alternatingFaceMapComplex A).map a) :=
  let ⟨b, hab, hba⟩ := ha
  ⟨{ hom := (alternatingFaceMapComplex A).map a
     inv := (alternatingFaceMapComplex A).map b
     homotopyHomInvId := (homotopic_alternatingFaceMapComplex_map_comp_id a b hab).some
     homotopyInvHomId := (homotopic_alternatingFaceMapComplex_map_comp_id b a hba).some }, rfl⟩

/-- **The normalized Moore complex of a homotopy equivalence of simplicial objects is a
homotopy equivalence of chain complexes.** Let `a : U ⟶ V` be a homotopy equivalence of
simplicial objects of an abelian category `A` ([Stacks, Tag 019N]). Then
`N(a) : N(U) ⟶ N(V)` is a homotopy equivalence of chain complexes. -/
@[stacks 019T "the second sentence, for the normalized Moore complex `N`; the first is \
  `homotopyEquivalences_alternatingFaceMapComplex_map` above, from which this one is deduced by \
  conjugating with the natural homotopy equivalence `inclusionOfMooreComplexMap`. Only \
  `Abelian A` is assumed, which provides the preadditivity the source's `additive` asks for. \
  Being a homotopy equivalence of chain complexes is \
  `HomologicalComplex.homotopyEquivalences`, which pins the map, and the hypothesis is 019N's \
  `SimplicialObject.homotopyEquivalences`"]
public theorem homotopyEquivalences_normalizedMooreComplex_map [Abelian A]
    (ha : SimplicialObject.homotopyEquivalences A a) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)
      ((normalizedMooreComplex A).map a) := by
  refine MorphismProperty.of_postcomp (W := HomologicalComplex.homotopyEquivalences A _) _
    (inclusionOfMooreComplexMap V) (homotopyEquivalences_inclusionOfMooreComplexMap V) ?_
  rw [normalizedMooreComplex_map_comp_inclusionOfMooreComplexMap]
  exact MorphismProperty.comp_mem _ _ _ (homotopyEquivalences_inclusionOfMooreComplexMap U)
    (homotopyEquivalences_alternatingFaceMapComplex_map ha)

end AlgebraicTopology

end

end
