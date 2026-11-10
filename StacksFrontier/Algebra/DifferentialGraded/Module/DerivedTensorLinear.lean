module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksCore.Tactic.StacksAttribute

/-! # The derived tensor product is linear over the base ring

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. The derived categories `D(A, d)` and `D(B, d)` are
`R`-linear (`DifferentialGradedModule.instLinearDerivedCategory`), and the derived tensor product
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of Tag 09LS is a functor between them. This file proves that it
is `R`-linear, which is the one clause of [Stacks, Tag 09S7] that the construction of the
equivalence in `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedEquivalenceBimodule.lean`
leaves out.

Linearity of a functor between `R`-linear categories is, by
`CategoryTheory.Functor.linear_iff`, the single family of identities
`F(r • 𝟙 X) = r • 𝟙 (F X)`. That reduces the question to the images of the scalar multiples of
the identities, and those can be followed down the three stages out of which `- ⊗_A^𝐋 N` is
built:

* on differential graded modules, `r • 𝟙 M` acts on a pure tensor `x ⊗ y` by `r • x ⊗ y`, which
  is `r` times `x ⊗ y` because the universal balanced map is `R`-bilinear;
* on `K(A, d)`, the comparison `DifferentialGraded.Bimodule.tensorCompFunctor_quotient` of Tag
  09LM transports that identity to the homotopy categories, whose quotient functors are
  `R`-linear;
* on `D(A, d)`, the comparison `- ⊗_A^𝐋 N → - ⊗_A N` of Tag 09LS is invertible at every object
  orthogonal on the left to the acyclic modules, and those objects resolve every object of
  `D(A, d)`, so the identity propagates there as well.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorFunctor_linear`: **Stacks 09S7**, the `R`-linearity
  of `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)`. It holds for every bimodule, with none of the three
  hypotheses of that tag.
* `DifferentialGraded.Bimodule.derivedTensorEquivalence_linear`: **Stacks 09S7**, the equivalence
  `D(A, d) ≌ D(B, d)` of that tag is an equivalence of `R`-linear triangulated categories: both
  it and its quasi-inverse are `R`-linear.
* `CategoryTheory.Functor.map_smul_id_of_iso`: the identity `F(r • 𝟙 X) = r • 𝟙 (F X)` only
  depends on the isomorphism class of `X`.

## Implementation notes

*Why the identities on scalar multiples of identities suffice.* In an `R`-linear category
`r • f = f ≫ (r • 𝟙)`, so a functor that respects the scalar multiples of the identities
respects every scalar multiple; this is `CategoryTheory.Functor.linear_iff`, and it is what makes
the argument below possible at all. The tensor differential graded functor of Tag 09LM is
produced by a choice (`DifferentialGraded.Bimodule.tensorDGFunctor`) and its action on morphisms
is only pinned down on pure tensors, so a direct computation of `F(r • f)` for a general `f` is
not available; `r • 𝟙` is the one morphism whose image can be computed from the data.

## References

* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7), whose conclusion is
  that `- ⊗_A^𝐋 N` is an `R`-linear equivalence of triangulated categories.
* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) for the tensor functor
  and [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) for its left derived functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

variable {R : Type*} [Semiring R] {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

/-- The identity `F(r • 𝟙 X) = r • 𝟙 (F X)` depends only on the isomorphism class of `X`: a
scalar multiple of an identity is conjugate to the corresponding one at any isomorphic object. -/
theorem Functor.map_smul_id_of_iso (F : C ⥤ D) {X Y : C} (e : X ≅ Y) (r : R)
    (h : F.map (r • 𝟙 Y) = r • 𝟙 (F.obj Y)) :
    F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  have hX : r • 𝟙 X = e.hom ≫ (r • 𝟙 Y) ≫ e.inv := by simp
  rw [hX, F.map_comp, F.map_comp, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← F.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]

/-- A linear functor carries `r • 𝟙 X` to `r • 𝟙 (F X)`. -/
private theorem Functor.map_smul_id (F : C ⥤ D) [F.Linear R] (X : C) (r : R) :
    F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

end CategoryTheory

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Tensoring with `N` carries the scalar multiple `r • 𝟙 M` of an identity of differential
graded `A`-modules to `r • 𝟙 (M ⊗_A N)`: on a pure tensor both sides send `x ⊗ y` to
`(r • x) ⊗ y`, and the universal balanced map is `R`-bilinear. -/
theorem tensorCompFunctor_map_smul_id (N : Bimodule A B) (M : DifferentialGradedModule A)
    (r : R) :
    (tensorCompFunctor N).map (r • 𝟙 M) = r • 𝟙 ((tensorCompFunctor N).obj M) := by
  refine tensorObj_hom_ext' N M _ _ fun x y => ?_
  refine (tensorCompFunctor_map_pure' N (r • 𝟙 M) x y).trans ?_
  change ((tensorDGFunctor N).pure M).toLinearMap (r • x) y = _
  rw [map_smul, LinearMap.smul_apply]
  rfl

/-- Tensoring with `N` on the homotopy categories carries `r • 𝟙 X` to `r • 𝟙 (X ⊗_A N)`. The
comparison `DifferentialGraded.Bimodule.tensorCompFunctor_quotient` of Tag 09LM identifies
`- ⊗_A N` followed by the quotient functor with the quotient functor followed by `- ⊗_A N`, and
the quotient functor is `R`-linear. -/
theorem tensorHomotopyFunctor_map_smul_id (N : Bimodule A B) (X : HomotopyCategory A) (r : R) :
    (tensorHomotopyFunctor N).map (r • 𝟙 X) = r • 𝟙 ((tensorHomotopyFunctor N).obj X) := by
  have hid : (toHomotopyCategory A).map (r • 𝟙 X.as) = r • 𝟙 X := by
    exact Functor.map_smul_id _ _ _
  let e := tensorCompFunctor_quotient N
  have hsrc : (tensorCompFunctor N ⋙ toHomotopyCategory B).map (r • 𝟙 X.as) =
      r • 𝟙 ((tensorCompFunctor N ⋙ toHomotopyCategory B).obj X.as) := by
    change (toHomotopyCategory B).map ((tensorCompFunctor N).map (r • 𝟙 X.as)) = _
    rw [tensorCompFunctor_map_smul_id]
    exact Functor.map_smul_id _ _ _
  have hnat := e.hom.naturality (r • 𝟙 X.as)
  rw [hsrc, Linear.smul_comp, Category.id_comp] at hnat
  refine (cancel_epi (e.hom.app X.as)).mp ?_
  rw [← hid, Linear.comp_smul]
  exact hnat.symm.trans (congrArg (r • ·) (Category.comp_id _).symm)

/-- Tensoring with `N` on `K(A, d)` followed by localization of `D(B, d)` carries `r • 𝟙 X` to
`r • 𝟙`, the localization functor being `R`-linear. -/
theorem tensorFunctorToDerivedCategory_map_smul_id (N : Bimodule A B) (X : HomotopyCategory A)
    (r : R) :
    (tensorFunctorToDerivedCategory N).map (r • 𝟙 X) =
      r • 𝟙 ((tensorFunctorToDerivedCategory N).obj X) := by
  change (quasiIsomorphisms' B).Q.map ((tensorHomotopyFunctor N).map (r • 𝟙 X)) = _
  rw [tensorHomotopyFunctor_map_smul_id]
  exact Functor.map_smul_id _ _ _

/-- The derived tensor product carries `r • 𝟙` to `r • 𝟙` at the image in `D(A, d)` of an object
of `K(A, d)` orthogonal on the left to the acyclic modules. At such an object the comparison
`- ⊗_A^𝐋 N → - ⊗_A N` is invertible, so the identity transfers from
`DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_map_smul_id` through its naturality
square. -/
theorem derivedTensorFunctor_map_smul_id_q (N : Bimodule A B) (X : HomotopyCategory A)
    (hX : (acyclic' A).leftOrthogonal X) (r : R) :
    (derivedTensorFunctor N).map (r • 𝟙 ((quasiIsomorphisms' A).Q.obj X)) =
      r • 𝟙 ((derivedTensorFunctor N).obj ((quasiIsomorphisms' A).Q.obj X)) := by
  have := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N X hX
  have hnat := (derivedTensorFunctorCounit N).naturality (r • 𝟙 X)
  rw [Functor.comp_map, Functor.map_smul_id, tensorFunctorToDerivedCategory_map_smul_id] at hnat
  refine (cancel_mono ((derivedTensorFunctorCounit N).app X)).mp (hnat.trans ?_)
  rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- **Stacks 09S7.** The derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is `R`-linear.

This holds for every differential graded `(A, B)`-bimodule `N`, with none of the hypotheses of
the tag: it is a property of the functor of Tag 09LS, not of the equivalence. Together with the
exactness recorded by `DifferentialGraded.Bimodule.derivedTensorFunctor_commShift` and
`DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated` (Tags 09LR and 09LS) it is
what makes the conclusion of Tag 09S7 an equivalence of `R`-linear triangulated categories.

Every object of `D(A, d)` is isomorphic to the image of an object of `K(A, d)` orthogonal on the
left to the acyclic modules, so `CategoryTheory.Functor.linear_iff` reduces the statement to
`DifferentialGraded.Bimodule.derivedTensorFunctor_map_smul_id_q`. -/
@[stacks 09S7 "the R-linearity of the functor - ⊗_A^𝐋 N"]
instance derivedTensorFunctor_linear (N : Bimodule A B) :
    (derivedTensorFunctor N).Linear R := by
  rw [Functor.linear_iff]
  intro X r
  have := Localization.essSurj (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
  obtain ⟨P, hP, s, hs⟩ := exists_quasiIso_leftOrthogonal_acyclic_homotopy A
    ((quasiIsomorphisms' A).Q.objPreimage X)
  have : IsIso ((quasiIsomorphisms' A).Q.map s) :=
    Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) s hs
  refine Functor.map_smul_id_of_iso _
    ((asIso ((quasiIsomorphisms' A).Q.map s) ≪≫
      (quasiIsomorphisms' A).Q.objObjPreimageIso X).symm) r ?_
  exact derivedTensorFunctor_map_smul_id_q N P hP r

/-- **Stacks 09S7.** Under the three hypotheses of that tag, the equivalence
`D(A, d) ≌ D(B, d)` of `DifferentialGraded.Bimodule.derivedTensorEquivalence` is `R`-linear in
both directions: its functor is `- ⊗_A^𝐋 N`, which is `R`-linear, and the quasi-inverse of an
`R`-linear equivalence is `R`-linear. -/
@[stacks 09S7 "the R-linearity of the equivalence and of its quasi-inverse"]
theorem derivedTensorEquivalence_linear (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorEquivalence N h2 h3).functor.Linear R ∧
      (derivedTensorEquivalence N h2 h3).inverse.Linear R := by
  have hfun : (derivedTensorEquivalence N h2 h3).functor.Linear R :=
    derivedTensorFunctor_linear N
  exact ⟨hfun, Equivalence.inverseLinear R _⟩

end DifferentialGraded.Bimodule

end
