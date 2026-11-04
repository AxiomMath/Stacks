module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction

/-!
# The distinguished triangles of the stupid filtration of a bounded complex

Let `A` be an abelian category with a derived category and let `K` be a cochain complex of
objects of `A`.  The brutal (stupid) truncations `σ^{≥p}K` of
`StacksFrontier/Algebra/Homology/StupidTruncation.lean` fit into short exact sequences of complexes

`0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ) ⟶ 0`

(`StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact`, degreewise split).  This
module turns each of them into a *distinguished triangle* of `D(A)`

`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ (σ^{≥p+1}K)⟦1⟧`,

and re-expresses the induction principle
`Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex` in terms of those
triangles.

The brutal truncation itself is Mathlib's `HomologicalComplex.stupidTrunc` of
`Mathlib/Algebra/Homology/Embedding/StupidTrunc.lean`, the inclusion `σ^{≥p}K ⟶ K` is
`HomologicalComplex.ιStupidTrunc`, and the triangles come from the short exact sequences through
`DerivedCategory.triangleOfSES_distinguished`.

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncGETriangle`: the triangle
  `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ (σ^{≥p+1}K)⟦1⟧` of `D(A)`.

## Main results

* `StacksDraft.StupidTruncation.stupidTruncGETriangle_distinguished`: it is distinguished.
* `StacksDraft.StupidTruncation.finite_support_stupidTruncGE`: a brutal truncation of a bounded
  complex is bounded, so the induction principle applies to it.
* `Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang`: the
  induction principle of `BoundedComplexInduction.lean` with the extension hypothesis phrased
  for a distinguished triangle rather than for a short exact sequence of complexes.
* `Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_stupidTruncGE`: the same
  conclusion for a brutal truncation `σ^{≥a}K` of a bounded complex, needing the property only
  at the terms `Kⁱ` with `a ≤ i`.

## Implementation notes

The extension hypothesis is `P T.obj₁ → P T.obj₃ → P T.obj₂`, the orientation in which the two
outer vertices of the filtration step — the next truncation and the single term — give the
truncation itself.  Nothing is lost by fixing the orientation: a property that has the other
two closure properties of a triangulated functor can rotate, since
`property_of_bounded_complex_of_distTriang` quantifies over all distinguished triangles and the
triangles of the filtration are available by name.

`property_of_bounded_complex_stupidTruncGE` is stated for a truncation `σ^{≥a}K` rather than
for `K` itself, so that the induction starts at the cut `a` and the property is never needed at
the terms of `K` below `a`.

`hzero` is a genuine separate hypothesis and not a consequence of `hext` and `hiso`: every
distinguished triangle through a zero object has that object among the two vertices the
extension step is allowed to assume, so no instance of `hext` reaches `P` at a zero object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

section Triangle

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] (K : CochainComplex A ℤ)

/-- The distinguished triangle of the stupid filtration of a cochain complex at `p`:

`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ (σ^{≥p+1}K)⟦1⟧`.

It is the triangle attached by `DerivedCategory.triangleOfSES` to the short exact sequence
`stupidTruncGEShortComplex`, which exhibits the bottom term of a brutal truncation as its
quotient by the next truncation. -/
noncomputable def stupidTruncGETriangle (p : ℤ) : Triangle (DerivedCategory A) :=
  DerivedCategory.triangleOfSES (stupidTruncGEShortComplex_shortExact K p)

/-- The triangle of the stupid filtration is distinguished. -/
theorem stupidTruncGETriangle_distinguished (p : ℤ) :
    stupidTruncGETriangle K p ∈ distTriang (DerivedCategory A) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- The first vertex of the filtration triangle at `p` is the truncation `σ^{≥p+1}K`. -/
@[simp]
theorem stupidTruncGETriangle_obj₁ (p : ℤ) :
    (stupidTruncGETriangle K p).obj₁ =
      DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE (p + 1))) :=
  rfl

/-- The second vertex of the filtration triangle at `p` is the truncation `σ^{≥p}K`. -/
@[simp]
theorem stupidTruncGETriangle_obj₂ (p : ℤ) :
    (stupidTruncGETriangle K p).obj₂ =
      DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE p)) :=
  rfl

/-- The third vertex of the filtration triangle is the degree-`p` term of `K` placed in
degree `p`. -/
@[simp]
theorem stupidTruncGETriangle_obj₃ (p : ℤ) :
    (stupidTruncGETriangle K p).obj₃ = (DerivedCategory.singleFunctor A p).obj (K.X p) :=
  rfl

/-- The first morphism of the filtration triangle at `p` is the image of the comparison
`σ^{≥p+1}K ⟶ σ^{≥p}K` of brutal truncations. -/
@[simp]
theorem stupidTruncGETriangle_mor₁ (p : ℤ) :
    (stupidTruncGETriangle K p).mor₁ =
      DerivedCategory.Q.map (stupidTruncGEMapLE K (show p ≤ p + 1 by omega)) :=
  rfl

/-- The second morphism of the filtration triangle at `p` is the image of the projection
`σ^{≥p}K ⟶ Kᵖ[-p]` onto the bottom term. -/
@[simp]
theorem stupidTruncGETriangle_mor₂ (p : ℤ) :
    (stupidTruncGETriangle K p).mor₂ = DerivedCategory.Q.map (stupidTruncGEπ K p) :=
  rfl

end Triangle

section Support

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
  (K : CochainComplex A ℤ)

/-- A brutal truncation `σ^{≥a}K` of a complex with finitely many non-zero terms again has
finitely many non-zero terms: in a degree `≥ a` its term is the corresponding term of `K`, and in
every other degree it vanishes. -/
theorem finite_support_stupidTruncGE (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (a : ℤ) :
    {i : ℤ | ¬ IsZero ((K.stupidTrunc (embeddingUpIntGE a)).X i)}.Finite := by
  refine hK.subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_cases hai : a ≤ i
  · exact fun h => hi (h.of_iso (stupidTruncGEXIso K a i hai))
  · exact (hi (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega))).elim

end Support

end StacksDraft.StupidTruncation

namespace Stacks.DerivedCategory.BoundedInduction

open StacksDraft.StupidTruncation

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **Induction on a bounded complex through the distinguished triangles of its stupid
filtration.**  A property of objects of `D(A)` invariant under isomorphism, holding at zero
objects, stable under the extension given by a distinguished triangle — from the first and third
vertices to the second — and holding at each term of a bounded complex `K` placed in its own
degree, holds at `K`.

This is `property_of_bounded_complex` with the extension hypothesis stated for the triangle that
`DerivedCategory.triangleOfSES` attaches to a short exact sequence of complexes rather than for
the sequence itself; the filtration steps realise it as `stupidTruncGETriangle`. -/
theorem property_of_bounded_complex_of_distTriang (P : DerivedCategory A → Prop)
    (hiso : ∀ {X Y : DerivedCategory A}, (X ≅ Y) → P X → P Y)
    (hzero : ∀ X : DerivedCategory A, IsZero X → P X)
    (hext : ∀ T : Triangle (DerivedCategory A), T ∈ distTriang (DerivedCategory A) →
      P T.obj₁ → P T.obj₃ → P T.obj₂)
    (K : CochainComplex A ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hsingle : ∀ i, P ((DerivedCategory.singleFunctor A i).obj (K.X i))) :
    P (DerivedCategory.Q.obj K) :=
  property_of_bounded_complex P hiso hzero
    (fun _ hS h₁ h₃ => hext _ (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃) K hK
    hsingle

/-- **The stupid filtration of a bounded complex, run from a cut.**  Under the hypotheses of
`property_of_bounded_complex_of_distTriang`, but with the property required at the terms `Kⁱ`
only for `a ≤ i`, the property holds at the brutal truncation `σ^{≥a}K`.

The terms of `σ^{≥a}K` in degrees below `a` vanish, so `hzero` covers them, and in degrees at
least `a` they are the terms of `K`. -/
theorem property_of_bounded_complex_stupidTruncGE (P : DerivedCategory A → Prop)
    (hiso : ∀ {X Y : DerivedCategory A}, (X ≅ Y) → P X → P Y)
    (hzero : ∀ X : DerivedCategory A, IsZero X → P X)
    (hext : ∀ T : Triangle (DerivedCategory A), T ∈ distTriang (DerivedCategory A) →
      P T.obj₁ → P T.obj₃ → P T.obj₂)
    (K : CochainComplex A ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (a : ℤ)
    (hsingle : ∀ i, a ≤ i → P ((DerivedCategory.singleFunctor A i).obj (K.X i))) :
    P (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE a))) := by
  refine property_of_bounded_complex_of_distTriang P hiso hzero hext _
    (finite_support_stupidTruncGE K hK a) fun i => ?_
  by_cases hai : a ≤ i
  · exact hiso ((DerivedCategory.singleFunctor A i).mapIso (stupidTruncGEXIso K a i hai).symm)
      (hsingle i hai)
  · exact hzero _ (Functor.map_isZero _
      (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega)))

end Stacks.DerivedCategory.BoundedInduction

end
