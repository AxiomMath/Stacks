module

public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic

/-!
# The cone of an isomorphism vanishes in the homotopy category

Let `(A, d)` be a differential graded algebra and let `f : K ⟶ L` be a homomorphism of right
differential graded `A`-modules whose class in the homotopy category `K(A)` is invertible — for
instance an identity, or any homotopy equivalence. Then the mapping cone of `f` is a zero object
of `K(A)`: the cone of an isomorphism is contractible.

The content is entirely Mathlib's, applied to this chapter's triangle: a distinguished triangle
has a zero third object exactly when its first morphism is invertible
(`CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`), and the triangle of a mapping
cone is distinguished by Tag 09KB together with Tag 09KH. The lemma is recorded here because it
is used repeatedly and nothing reusable existed: Tag 09JW's proof
(`DifferentialGradedModule.exists_factorization_isAdmissibleMono`) relies on the contractibility
of the cone of `𝟙 K` but states it only in prose and exposes neither direction of it.

## Main results

* `DifferentialGradedModule.isZero_toHomotopyCategory_mappingCone_of_isIso`: the cone of a
  homomorphism that becomes invertible in `K(A)` is a zero object of `K(A)`.
* `DifferentialGradedModule.isZero_toHomotopyCategory_mappingCone_id`: in particular the cone of
  an identity is a zero object of `K(A)`.
* `DifferentialGradedModule.toHomotopyCategory_map_eq_zero_of_mappingCone_id_source`,
  `..._of_mappingCone_id_target` and
  `DifferentialGradedModule.toHomotopyCategory_map_eq_zero_of_factors_mappingCone_id`:
  consequently every homomorphism out of, into, or factoring through the cone of an identity is
  null-homotopic. The last is the form in which contractibility is consumed: a null-homotopy of
  a homomorphism is the same thing as a factorization of it through such a cone, and this is the
  easy half of that correspondence.

## Implementation notes

*Why `IsIso` of the image rather than of `f`.* The hypothesis is that `f` becomes invertible in
`K(A)`, not that it is invertible in the category of differential graded modules. That is the
weaker and the useful condition — it holds for every homotopy equivalence — and it is what
`Triangle.isZero₃_iff_isIso₁` asks of `(mappingConeTriangle f).mor₁`, which is by construction
the image of `f` under the quotient functor.

*Universes.* The universe parameters of `DifferentialGradedAlgebra` and of
`DifferentialGradedModule` — the base ring, the algebra and the module each carrying their own —
are left to be inferred here, since nothing below relates them.

## References

* [Stacks Project, Tag 09KB](https://stacks.math.columbia.edu/tag/09KB), the triangle of a
  mapping cone; [Tag 09KH](https://stacks.math.columbia.edu/tag/09KH), the pretriangulated
  structure; the contractibility of the cone of an identity is used in
  [Tag 09JW](https://stacks.math.columbia.edu/tag/09JW).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The mapping cone of a homomorphism whose class in `K(A)` is invertible is a zero object of
`K(A)`. In particular the cone of a homotopy equivalence is contractible. -/
theorem isZero_toHomotopyCategory_mappingCone_of_isIso {K L : DifferentialGradedModule A}
    (f : K ⟶ L) (hf : IsIso ((toHomotopyCategory A).map f)) :
    IsZero ((toHomotopyCategory A).obj (coneModule f)) :=
  (Triangle.isZero₃_iff_isIso₁ (mappingConeTriangle f)
    (mem_distTriang_of_isDistinguishedTriangle A
      (isDistinguishedTriangle_mappingConeTriangle A f))).2 hf

/-- The mapping cone of an identity is a zero object of the homotopy category. -/
theorem isZero_toHomotopyCategory_mappingCone_id (K : DifferentialGradedModule A) :
    IsZero ((toHomotopyCategory A).obj (coneModule (𝟙 K))) :=
  isZero_toHomotopyCategory_mappingCone_of_isIso A (𝟙 K)
    (by rw [CategoryTheory.Functor.map_id]; infer_instance)

/-- A homomorphism out of the cone of an identity is null-homotopic, since that cone is a zero
object of the homotopy category. -/
theorem toHomotopyCategory_map_eq_zero_of_mappingCone_id_source
    {K M : DifferentialGradedModule A} (u : coneModule (𝟙 K) ⟶ M) :
    (toHomotopyCategory A).map u = 0 :=
  (isZero_toHomotopyCategory_mappingCone_id A K).eq_of_src _ _

/-- A homomorphism into the cone of an identity is null-homotopic, since that cone is a zero
object of the homotopy category. -/
theorem toHomotopyCategory_map_eq_zero_of_mappingCone_id_target
    {K M : DifferentialGradedModule A} (u : M ⟶ coneModule (𝟙 K)) :
    (toHomotopyCategory A).map u = 0 :=
  (isZero_toHomotopyCategory_mappingCone_id A K).eq_of_tgt _ _

/-- Any homomorphism factoring through the cone of an identity vanishes in the homotopy
category. This is the easy half of the correspondence between null-homotopies of a homomorphism
and factorizations of it through such a cone. -/
theorem toHomotopyCategory_map_eq_zero_of_factors_mappingCone_id
    {K M N : DifferentialGradedModule A} (v : M ⟶ coneModule (𝟙 K))
    (w : coneModule (𝟙 K) ⟶ N) (u : M ⟶ N) (hu : u = v ≫ w) :
    (toHomotopyCategory A).map u = 0 := by
  rw [hu, CategoryTheory.Functor.map_comp,
    toHomotopyCategory_map_eq_zero_of_mappingCone_id_target A v, zero_comp]

end DifferentialGradedModule

end
