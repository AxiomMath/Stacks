module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.MonoidalStructure
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.Algebra.Field.Rat
public import Mathlib.CategoryTheory.Linear.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The category of Chow motives

A Chow motive over `k` is a triple `(X, p, m)` with `X` a smooth projective scheme over `k`,
`p ∈ Corr⁰(X, X)` a projector and `m ∈ ℤ` a Tate twist, and a morphism of motives is an element
of `q ∘ Corr^{n-m}(X, Y) ∘ p`. That is exactly an object of the Karoubi envelope of the category
of correspondences: an object together with an idempotent endomorphism of it, with the morphisms
cut out by the two idempotents. The category `M_k` of Chow motives is therefore the Karoubi
envelope of the category of correspondences, and the functor `h` is the graph functor followed
by the canonical embedding, `h(X) = (X, 1, 0)` and `h(f) = [Γ_f]`.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.instModule`: the morphism modules of the Karoubi envelope
  of an `R`-linear category.
* `Stacks.WeilCohomology.CorrespondenceStructure.Motive`: the category `M_k` of Chow motives.
* `Stacks.WeilCohomology.CorrespondenceStructure.graphFunctor`: the graph functor
  `X ↦ X`, `f ↦ [Γ_f]` into the category of correspondences.
* `Stacks.WeilCohomology.CorrespondenceStructure.motiveFunctor`: the functor `h`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.linear`: the Karoubi envelope of an `R`-linear category is
  `R`-linear.
* `Stacks.WeilCohomology.CorrespondenceStructure.hom_motive_iff`: the morphisms of `M_k` from
  `(X, p, m)` to `(Y, q, n)` are exactly the correspondences of the form `q ∘ c ∘ p`.
* `Stacks.WeilCohomology.CorrespondenceStructure.motiveFunctor_obj_p` and
  `Stacks.WeilCohomology.CorrespondenceStructure.motiveFunctor_map_f`: `h(X) = (X, 1, 0)` and
  `h(f) = [Γ_f]`.
* `Stacks.WeilCohomology.CorrespondenceStructure.linear`: `M_k` is a `ℚ`-linear category.

## Implementation notes

**Where the twist lives.** `Stacks.WeilCohomology.CorrespondenceStructure` carries a category of
correspondences on the objects of a symmetric monoidal category `C`, with one degree of
correspondences at a time. Taking `C` to be the smooth projective schemes over `k` enlarged by
the Tate twists, so that an object is a pair `(X, m)` and `Hom((X, m), (Y, n))` is
`Corr^{n-m}(X, Y)`, an object of the Karoubi envelope is a triple `(X, p, m)` with `p` a
projector in `Corr⁰(X, X)` — the source's motive, with the projector automatically of degree
zero — and the morphism sets are the source's. Only the degree-zero part of the ambient category
is visible to `Karoubi`, which is why no grading has to be carried here.

**Relation to the other formalisation of a motive in this library.**
`Stacks.WeilCohomology.ChowMotive` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups` is a bundled triple
`(X, p, m)` of a scheme, a projector and a twist relative to a carried
`Stacks.WeilCohomology.CorrespondenceCalculus`, built for Stacks 0FGL to define the Chow groups
`CH^i(M)` of a motive. It records no morphism sets, no composition of morphisms of motives and
no categorical structure, and so is not a category of motives; the two are complementary, the
present file supplying the category and the functor `h` of Stacks 0FGA and that one the Chow
groups of a single motive.

**The `ℚ`-linear structure, and the monoidal structure.** The ℚ-linear structure of the morphism
spaces of correspondences is not part of `CorrespondenceStructure`, which carries only what the
monoidal axioms of Stacks 0FG7 use; it is the content of Stacks 0FG2, carried there by
`Stacks.WeilCohomology.GradedCompositionData` for the category of all degrees at once. It enters
`Stacks.WeilCohomology.CorrespondenceStructure.linear` as an instance hypothesis on the
single-degree category, and what is proved is the step that Stacks 0FGA actually needs: passing
from an `R`-linear category to its Karoubi envelope. The symmetric monoidal structure of `M_k`
is Stacks 0FGC and is not constructed here; the monoidal structure used by the duality of Stacks
0FGI is base's monoidal structure on the category of correspondences itself, Stacks 0FG7.

## References

* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FGL](https://stacks.math.columbia.edu/tag/0FGL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents MonoidalCategory

universe v u w

namespace CategoryTheory.Idempotents.Karoubi

section Hom

variable {C : Type u} [Category.{v} C]

/-- A morphism of the underlying category is a morphism of the Karoubi envelope exactly when it
factors through the two idempotents: `Hom((X, p), (Y, q)) = q ∘ Hom(X, Y) ∘ p`. -/
theorem comm_iff_exists {P Q : Karoubi C} (f : P.X ⟶ Q.X) :
    P.p ≫ f ≫ Q.p = f ↔ ∃ c : P.X ⟶ Q.X, f = P.p ≫ c ≫ Q.p := by
  refine ⟨fun h => ⟨f, h.symm⟩, fun h => ?_⟩
  obtain ⟨c, rfl⟩ := h
  simp

end Hom

section Linear

variable {R : Type*} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Scalar multiplication on a morphism module of the Karoubi envelope of an `R`-linear
category: the two idempotents absorb it because composition is `R`-bilinear. -/
local instance instSMul {P Q : Karoubi C} : SMul R (P ⟶ Q) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp, Linear.comp_smul, f.comm]⟩

@[simp]
theorem smul_f {P Q : Karoubi C} (r : R) (f : P ⟶ Q) : (r • f).f = r • f.f :=
  rfl

/-- The morphisms of the Karoubi envelope of an `R`-linear category form an `R`-module, the
structure being inherited from the morphisms of the underlying category. -/
local instance instModule {P Q : Karoubi C} : Module R (P ⟶ Q) :=
  Function.Injective.module R (inclusionHom P Q) (fun _ _ h => hom_ext _ _ h) fun _ _ => rfl

/-- The Karoubi envelope of an `R`-linear category is `R`-linear. -/
local instance linear : Linear R (Karoubi C) where
  homModule _ _ := instModule
  smul_comp _ _ _ _ _ _ := hom_ext _ _ (by simp)
  comp_smul _ _ _ _ _ _ := hom_ext _ _ (by simp)

end Linear

end CategoryTheory.Idempotents.Karoubi

namespace Stacks.WeilCohomology

namespace CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]

/-- **Stacks Project, Tag 0FGA.** The category `M_k` of Chow motives over `k`: the Karoubi
envelope of the category of correspondences. An object is a pair of an object of the ambient
category — a smooth projective scheme together with its Tate twist — and a projector in
`Corr⁰(X, X)`, that is a triple `(X, p, m)`; a morphism `(X, p, m) ⟶ (Y, q, n)` is a
correspondence in `Corr^{n-m}(X, Y)` fixed by the two projectors. -/
@[stacks 0FGA "the category M_k of Chow motives over k, whose objects are the triples (X,p,m)"]
abbrev Motive (S : CorrespondenceStructure.{v, u, w} D) :=
  Karoubi S.Obj

/-- **Stacks Project, Tag 0FGA.** The morphisms of `M_k` are the correspondences cut out by the
two projectors: `Hom((X, p, m), (Y, q, n)) = q ∘ Corr^{n-m}(X, Y) ∘ p`. -/
@[stacks 0FGA "Hom((X,p,m),(Y,q,n)) = q o Corr^{n-m}(X,Y) o p"]
theorem hom_motive_iff (S : CorrespondenceStructure.{v, u, w} D) {M N : S.Motive}
    (c : M.X ⟶ N.X) :
    (∃ f : M ⟶ N, f.f = c) ↔ ∃ c₀ : M.X ⟶ N.X, c = M.p ≫ c₀ ≫ N.p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨f, rfl⟩ := h
    exact (Karoubi.comm_iff_exists f.f).1 f.comm
  · exact ⟨⟨c, (Karoubi.comm_iff_exists c).2 h⟩, rfl⟩

/-- The graph functor into the category of correspondences: the identity on objects, and
`f ↦ [Γ_f]` on morphisms. -/
def graphFunctor (S : CorrespondenceStructure.{v, u, w} D) : D ⥤ S.Obj where
  obj X := Obj.mk X
  map f := S.graph f
  map_id X := S.graph_id X
  map_comp f g := S.graph_comp f g

/-- **Stacks Project, Tag 0FGA.** The functor `h` of Stacks 0FGA, from the ambient category of
smooth projective schemes over `k` to the category of Chow motives: `h(X) = (X, 1, 0)` is the
motive of `X` with the identity as projector and no twist, and `h(f) = [Γ_f]` is the graph of a
morphism.

The source's `h` is contravariant on schemes, `h(f) = [Γ_f] ∈ Corr⁰(X, Y)` for `f : Y → X`,
while `Stacks.WeilCohomology.CorrespondenceStructure.graph` is covariant on the ambient
category; so the ambient category here is the opposite of the category of smooth projective
schemes over `k` enlarged by the Tate twists, and `h` is then the source's functor. -/
@[stacks 0FGA "the functor h into M_k, with h(X) = (X,1,0) and h(f) = [Gamma_f]"]
def motiveFunctor (S : CorrespondenceStructure.{v, u, w} D) : D ⥤ S.Motive :=
  S.graphFunctor ⋙ toKaroubi S.Obj

@[simp]
theorem motiveFunctor_obj_X (S : CorrespondenceStructure.{v, u, w} D) (X : D) :
    (S.motiveFunctor.obj X).X = Obj.mk X :=
  rfl

/-- The projector of the motive `h(X)` is the identity correspondence, the diagonal class: in
the notation of the source `h(X) = (X, 1, 0)`. -/
@[simp]
theorem motiveFunctor_obj_p (S : CorrespondenceStructure.{v, u, w} D) (X : D) :
    (S.motiveFunctor.obj X).p = S.id X :=
  rfl

/-- The morphism `h(f)` is the graph of `f`: in the notation of the source `h(f) = [Γ_f]`. -/
@[simp]
theorem motiveFunctor_map_f (S : CorrespondenceStructure.{v, u, w} D) {X Y : D} (f : X ⟶ Y) :
    (S.motiveFunctor.map f).f = S.graph f :=
  rfl

/-- **Stacks Project, Tag 0FGA.** The category `M_k` of Chow motives is `ℚ`-linear, the
category of correspondences being so. The `ℚ`-linear structure of the correspondence spaces is
the content of Stacks 0FG2 and enters as a hypothesis; what is proved is that it passes to the
Karoubi envelope. -/
@[stacks 0FGA "M_k is a Q-linear category, given the Q-linear structure on correspondences",
  instance_reducible]
def linear (S : CorrespondenceStructure.{v, u, w} D) [Preadditive S.Obj] [Linear ℚ S.Obj] :
    Linear ℚ S.Motive :=
  Karoubi.linear

end CorrespondenceStructure

end Stacks.WeilCohomology

end
