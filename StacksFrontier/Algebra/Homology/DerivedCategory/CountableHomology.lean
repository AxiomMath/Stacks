module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.DifferentialGraded.Module.CountableCohomology

/-!
# Countable homology in the derived category of a ring

Let `R` be a ring. An object of `D(R)` **has countable homology** when every one of its homology
modules has a countable underlying set. This file collects the closure properties of that
condition that the long exact homology sequence supplies: it is invariant under isomorphism, it
holds at a zero object, it is stable under binary biproducts, and it satisfies two-out-of-three
along a distinguished triangle.

Together these are what a Mayer--Vietoris induction over the quasi-compact opens of a scheme
consumes. In the glueing step of [Stacks, Tag 0CRP] the complexes `RΓ(V, K)`, `RΓ(W, K)` and
`RΓ(V ∩ W, K)` sit with `RΓ(V ∪ W, K)` in a distinguished triangle whose middle term is the
biproduct of the first two, so countability of the cohomology over `V`, `W` and `V ∩ W` yields
countability over `V ∪ W`. The hypercohomology `H^i(U, -)` of a quasi-compact open of a scheme is
the homology of an object of `D(Γ(X, U))`, which is why the statements here are about the derived
category of a ring.

## Main definitions

* `Stacks.Homology.HasCountableHomology`: every homology module of an object of `D(R)` is
  countable.

## Main results

* `Stacks.Homology.HasCountableHomology.of_iso`: invariance under isomorphism.
* `Stacks.Homology.HasCountableHomology.of_isZero`: a zero object has countable homology.
* `Stacks.Homology.HasCountableHomology.biprod`: stability under binary biproducts.
* `Stacks.Homology.HasCountableHomology.obj₁`, `Stacks.Homology.HasCountableHomology.obj₂`,
  `Stacks.Homology.HasCountableHomology.obj₃`: along a distinguished triangle, countable homology
  at two of the three vertices forces it at the third.

## Implementation notes

Countability is Mathlib's `Countable` typeclass on the carrier of a module, so the condition is a
condition on the underlying types of the homology modules; it transfers along an isomorphism
because an isomorphism of modules is injective on carriers.

The two-out-of-three results are the three exactness statements of the long exact homology
sequence of a distinguished triangle — `DerivedCategory.HomologySequence.exact₁`, `exact₂` and
`exact₃` — fed into `CategoryTheory.ShortComplex.countable_X₂`, which bounds the middle term of an
exact sequence of modules by its outer terms. Only exactness at one spot is used in each case, so
no short exact sequence and no splitting is involved.

Stability under binary biproducts is deduced from `obj₂` applied to the split triangle
`X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`, which is distinguished in any pretriangulated category, rather than
from additivity of the homology functors; that way the biproduct case needs no separate argument
about products of modules.

The ring and the modules are in the same universe, as they are in
`CategoryTheory.ShortComplex.countable_X₂`; the universe of the derived category is left free.

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
* [Stacks Project, Tag 0CRM](https://stacks.math.columbia.edu/tag/0CRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace Stacks.Homology

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The middle term of an exact sequence of modules whose outer terms are countable is countable,
with the two countability conditions taken as explicit arguments rather than as instances. This is
`CategoryTheory.ShortComplex.countable_X₂` in the shape in which the exactness statements of a
long exact homology sequence present themselves: the short complex is determined by the exactness
proof, and the countability of its outer terms is then supplied positionally. -/
private theorem countable_X₂_of_exact {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    (h₁ : Countable S.X₁) (h₃ : Countable S.X₃) : Countable S.X₂ :=
  have := h₁
  have := h₃
  ShortComplex.countable_X₂ S hS

/-- An object of the derived category of `R`-modules **has countable homology** when all of its
homology modules are countable. -/
def HasCountableHomology (E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∀ i : ℤ, Countable ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj E)

/-- Having countable homology is invariant under isomorphism: homology is functorial, and an
isomorphism of modules is injective on carriers. -/
theorem HasCountableHomology.of_iso {E F : DerivedCategory (ModuleCat.{u} R)} (e : E ≅ F)
    (h : HasCountableHomology E) : HasCountableHomology F := fun i => by
  have := h i
  have hmono : Mono
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e).inv :=
    inferInstance
  exact Function.Injective.countable ((ModuleCat.mono_iff_injective _).1 hmono)

/-- A zero object has countable homology: all of its homology modules are zero, hence
subsingletons. -/
theorem HasCountableHomology.of_isZero {E : DerivedCategory (ModuleCat.{u} R)} (h : IsZero E) :
    HasCountableHomology E := fun i => by
  have hz : IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj E) :=
    Functor.map_isZero _ h
  have : Subsingleton
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj E) := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z, z = (0 : (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj E) :=
      fun z => by
        have := hz.eq_of_tgt (𝟙 _) 0
        simpa using congrArg (fun f => f z) (congrArg ModuleCat.Hom.hom this)
    rw [hx x, hx y]
  have : Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj E) :=
    Finite.of_subsingleton
  infer_instance

/-- **Two out of three at the first vertex.** If the second and third vertices of a distinguished
triangle have countable homology, so does the first: the homology sequence is exact at
`H^i(X₁)`, between `H^{i-1}(X₃)` and `H^i(X₂)`. -/
theorem HasCountableHomology.obj₁ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₂ : HasCountableHomology T.obj₂)
    (h₃ : HasCountableHomology T.obj₃) : HasCountableHomology T.obj₁ := fun i =>
  countable_X₂_of_exact
    (_root_.DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega))
    (h₃ (i - 1)) (h₂ i)

/-- **Two out of three at the second vertex.** If the first and third vertices of a distinguished
triangle have countable homology, so does the second: the homology sequence is exact at
`H^i(X₂)`, between `H^i(X₁)` and `H^i(X₃)`. -/
theorem HasCountableHomology.obj₂ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : HasCountableHomology T.obj₁)
    (h₃ : HasCountableHomology T.obj₃) : HasCountableHomology T.obj₂ := fun i =>
  countable_X₂_of_exact (_root_.DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i)

/-- **Two out of three at the third vertex.** If the first and second vertices of a distinguished
triangle have countable homology, so does the third: the homology sequence is exact at
`H^i(X₃)`, between `H^i(X₂)` and `H^{i+1}(X₁)`. -/
theorem HasCountableHomology.obj₃ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : HasCountableHomology T.obj₁)
    (h₂ : HasCountableHomology T.obj₂) : HasCountableHomology T.obj₃ := fun i =>
  countable_X₂_of_exact
    (_root_.DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl) (h₂ i) (h₁ (i + 1))

/-- Having countable homology is stable under binary biproducts: the split triangle
`X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧` is distinguished, so this is the two-out-of-three statement at its
middle vertex. -/
theorem HasCountableHomology.biprod {E F : DerivedCategory (ModuleCat.{u} R)}
    (hE : HasCountableHomology E) (hF : HasCountableHomology F) :
    HasCountableHomology (E ⊞ F) :=
  HasCountableHomology.obj₂ (binaryBiproductTriangle E F)
    (binaryBiproductTriangle_distinguished E F) hE hF

end Stacks.Homology

end
