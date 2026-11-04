module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategoryLimits
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions

/-!
# Orthogonality to the acyclic differential graded modules

Let `(A, d)` be a differential graded algebra and let `K(A)` be the homotopy category of right
differential graded `A`-modules. The modules orthogonal on the left, resp. on the right, to the
acyclic ones — those `P` with `Hom_{K(A)}(P, N) = 0`, resp. those `I` with
`Hom_{K(A)}(N, I) = 0`, for every acyclic `N` — are what the construction of the derived
functors out of `K(A)` is built on: they are the collections to which Stacks 06XN is applied,
and Stacks 09KM, resp. 09KS, says that the modules with property (P), resp. property (I),
belong to them.

This file provides the closure properties by which such a membership is actually established.
Both orthogonals are triangulated subcategories of `K(A)`, so they are closed under extensions;
the point of the lemmas below is to put that in terms of the *admissible short exact sequences*
of differential graded modules, which is the only form in which an extension is ever presented
in this chapter, by way of the triangle of Stacks 09K8. The left orthogonal is in addition
closed under direct sums and the right orthogonal under products, which is what a filtration
with direct-sum graded pieces needs.

## Main results

* `DifferentialGradedModule.mem_distTriang_of_isDistinguishedTriangle`: the chapter's predicate
  `IsDistinguishedTriangle` is membership in Mathlib's class of distinguished triangles of the
  pretriangulated structure of Stacks 09KH.
* `DifferentialGradedModule.associatedTriangle_mem_distTriang`: the triangle attached to an
  admissible short exact sequence is distinguished in that sense.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_isAdmissibleShortExact` and
  `rightOrthogonal_acyclic_of_isAdmissibleShortExact`: the middle term of an admissible short
  exact sequence whose outer terms are orthogonal to the acyclic modules is orthogonal to them.
* `DifferentialGradedModule.leftOrthogonal_acyclic_quotient_of_isAdmissibleShortExact` and
  `rightOrthogonal_acyclic_sub_of_isAdmissibleShortExact`: the other two positions of the
  sequence, which is what a telescope presentation needs, the module it presents being the
  quotient.
* `DifferentialGradedModule.leftOrthogonal_acyclic_stage_of_admissibleFiltration`: every stage
  of a filtration by admissible monomorphisms is orthogonal on the left, as soon as the bottom
  stage and all the successive quotients are. Its dual
  `rightOrthogonal_acyclic_stage_of_admissibleFiltration` does the same for a decreasing
  filtration, where the induction runs over the quotients `I / F i` rather than the stages.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_iso` and `rightOrthogonal_acyclic_of_iso`:
  transfer along an isomorphism of differential graded modules.
* `DifferentialGradedModule.leftOrthogonal_acyclic_sigma` and
  `rightOrthogonal_acyclic_pi`: direct sums, resp. products, of orthogonal objects of `K(A)` are
  orthogonal.

## Implementation notes

*Which notion of distinguished triangle.* The pretriangulated structure on `K(A)` is the one
chosen by `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, and the only property
of that choice a client may use is `DifferentialGradedModule.distinguishedTriangles_eq`, which
identifies its distinguished triangles with `DifferentialGradedModule.IsDistinguishedTriangle`.
Everything below goes through that equality, so no second pretriangulated structure is
introduced and no property of the chosen one beyond the stated equality is relied upon.

*Universes.* The differential graded algebra and its modules live in a single universe:
`DifferentialGradedAlgebra : Type u → Type u`, and a module over it again lies in `Type u`. The
Stacks source is universe-polymorphic in the algebra and the module separately. Nothing below
depends on the universes being equal, so allowing separate universes would add universe
parameters without changing the content.

## References

* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) and
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS) are the two statements these closure
  properties serve; the triangle of an admissible short exact sequence is
  [Tag 09K8](https://stacks.math.columbia.edu/tag/09K8), and the vanishing criterion along a
  distinguished triangle is [Tag 0149](https://stacks.math.columbia.edu/tag/0149).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The chapter's predicate `IsDistinguishedTriangle` is membership in the class of
distinguished triangles of the chosen pretriangulated structure on `K(A)`. -/
theorem mem_distTriang_of_isDistinguishedTriangle
    {T : Pretriangulated.Triangle (HomotopyCategory A)} (hT : IsDistinguishedTriangle A T) :
    T ∈ distTriang (HomotopyCategory A) := by
  rwa [distinguishedTriangles_eq]

/-- The triangle attached to an admissible short exact sequence of differential graded modules
is a distinguished triangle of `K(A)`. -/
theorem associatedTriangle_mem_distTriang {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) (hfg : IsAdmissibleShortExact f g) :
    associatedTriangle A f g hfg ∈ distTriang (HomotopyCategory A) :=
  mem_distTriang_of_isDistinguishedTriangle A
    (isDistinguishedTriangle_associatedTriangle A f g hfg)

/-- **Stacks 0149** for the left orthogonal, in the form this chapter supplies extensions. If
the outer terms of an admissible short exact sequence are orthogonal on the left to the acyclic
differential graded modules, so is the middle term. -/
theorem leftOrthogonal_acyclic_of_isAdmissibleShortExact {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) (hfg : IsAdmissibleShortExact f g)
    (hK : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj K))
    (hM : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj L) :=
  (acyclic' A).leftOrthogonal.ext_of_isTriangulatedClosed₂ _
    (associatedTriangle_mem_distTriang A f g hfg) hK hM

/-- **Stacks 0149** for the right orthogonal. If the outer terms of an admissible short exact
sequence are orthogonal on the right to the acyclic differential graded modules, so is the
middle term. -/
theorem rightOrthogonal_acyclic_of_isAdmissibleShortExact {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) (hfg : IsAdmissibleShortExact f g)
    (hK : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj K))
    (hM : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj L) :=
  (acyclic' A).rightOrthogonal.ext_of_isTriangulatedClosed₂ _
    (associatedTriangle_mem_distTriang A f g hfg) hK hM

/-- The quotient in an admissible short exact sequence whose other two terms are orthogonal on
the left to the acyclic modules is orthogonal on the left to them. This is the step by which
a telescope presentation transfers orthogonality to the module it presents. -/
theorem leftOrthogonal_acyclic_quotient_of_isAdmissibleShortExact
    {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) (hfg : IsAdmissibleShortExact f g)
    (hK : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj K))
    (hL : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj L)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) :=
  (acyclic' A).leftOrthogonal.ext_of_isTriangulatedClosed₃ _
    (associatedTriangle_mem_distTriang A f g hfg) hK hL

/-- The sub in an admissible short exact sequence whose other two terms are orthogonal on the
right to the acyclic modules is orthogonal on the right to them. -/
theorem rightOrthogonal_acyclic_sub_of_isAdmissibleShortExact
    {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) (hfg : IsAdmissibleShortExact f g)
    (hL : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj L))
    (hM : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj K) :=
  (acyclic' A).rightOrthogonal.ext_of_isTriangulatedClosed₁ _
    (associatedTriangle_mem_distTriang A f g hfg) hL hM

/-- Orthogonality on the left to the acyclic modules transfers along an isomorphism of
differential graded modules. -/
theorem leftOrthogonal_acyclic_of_iso {M N : DifferentialGradedModule A} (e : M ≅ N)
    (hM : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj N) :=
  (acyclic' A).leftOrthogonal.prop_of_iso ((toHomotopyCategory A).mapIso e) hM

/-- Orthogonality on the right to the acyclic modules transfers along an isomorphism of
differential graded modules. -/
theorem rightOrthogonal_acyclic_of_iso {M N : DifferentialGradedModule A} (e : M ≅ N)
    (hM : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj N) :=
  (acyclic' A).rightOrthogonal.prop_of_iso ((toHomotopyCategory A).mapIso e) hM

/-- An exhaustive filtration whose bottom stage and whose successive quotients are orthogonal on
the left to the acyclic differential graded modules has every stage orthogonal on the left to
them. The inclusions are presented as the monomorphisms of admissible short exact sequences,
which is the form in which a property-(P) filtration provides them. -/
theorem leftOrthogonal_acyclic_stage_of_admissibleFiltration
    (F : ℕ → DifferentialGradedModule A) (Q : ℕ → DifferentialGradedModule A)
    (incl : ∀ i, Hom (F i) (F (i + 1))) (quot : ∀ i, Hom (F (i + 1)) (Q i))
    (hses : ∀ i, IsAdmissibleShortExact (incl i) (quot i))
    (hbot : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (F 0)))
    (hQ : ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (Q i))) :
    ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (F i))
  | 0 => hbot
  | i + 1 =>
    leftOrthogonal_acyclic_of_isAdmissibleShortExact A (incl i) (quot i) (hses i)
      (leftOrthogonal_acyclic_stage_of_admissibleFiltration F Q incl quot hses hbot hQ i)
      (hQ i)

/-- The dual of `leftOrthogonal_acyclic_stage_of_admissibleFiltration`, for a *decreasing*
filtration. If the bottom quotient and every graded piece are orthogonal on the right to the
acyclic differential graded modules, then so is every quotient `Q i`. The graded pieces are
presented as the subs of admissible short exact sequences `P i ⟶ Q (i + 1) ⟶ Q i`, which is the
form in which a property-(I) filtration provides them: `P i` is `F i / F (i + 1)` and `Q i` is
`I / F i`. -/
theorem rightOrthogonal_acyclic_stage_of_admissibleFiltration
    (Q : ℕ → DifferentialGradedModule A) (P : ℕ → DifferentialGradedModule A)
    (sub : ∀ i, Hom (P i) (Q (i + 1))) (proj : ∀ i, Hom (Q (i + 1)) (Q i))
    (hses : ∀ i, IsAdmissibleShortExact (sub i) (proj i))
    (hbot : (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (Q 0)))
    (hP : ∀ i, (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (P i))) :
    ∀ i, (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (Q i))
  | 0 => hbot
  | i + 1 =>
    rightOrthogonal_acyclic_of_isAdmissibleShortExact A (sub i) (proj i) (hses i) (hP i)
      (rightOrthogonal_acyclic_stage_of_admissibleFiltration Q P sub proj hses hbot hP i)

/-- A direct sum in `K(A)` of modules orthogonal on the left to the acyclic modules is
orthogonal on the left to them. -/
theorem leftOrthogonal_acyclic_sigma {ι : Type u} (X : ι → HomotopyCategory A)
    (hX : ∀ i, (acyclic' A).leftOrthogonal (X i)) : (acyclic' A).leftOrthogonal (∐ X) :=
  (acyclic' A).leftOrthogonal_sigma X hX

/-- A product in `K(A)` of modules orthogonal on the right to the acyclic modules is orthogonal
on the right to them. -/
theorem rightOrthogonal_acyclic_pi {ι : Type u} (X : ι → HomotopyCategory A)
    (hX : ∀ i, (acyclic' A).rightOrthogonal (X i)) : (acyclic' A).rightOrthogonal (∏ᶜ X) :=
  (acyclic' A).rightOrthogonal_pi X hX

end DifferentialGradedModule

end
