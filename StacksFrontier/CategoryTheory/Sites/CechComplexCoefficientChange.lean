module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# Changing the coefficient category of a Čech complex

Mathlib's `CategoryTheory.cechComplexFunctor` takes a family `U : ι → C` and a presheaf
`P : Cᵒᵖ ⥤ A` and returns a cochain complex in `A`. The degree `n` term is the product, indexed by
the tuples `x : Fin (n + 1) → ι`, of the sections of `P` over `inter U x`, and the differential is
an alternating sum of restriction maps.

Both constructions are preserved by an additive functor `G : A ⥤ B` which preserves products of the
relevant size: the product because `G` preserves it, the alternating sum because `G` is additive.
So the `G`-image of the Čech complex of `P` is isomorphic, as a cochain complex, to the Čech
complex of `P ⋙ G`, and a Čech cohomology object of `P ⋙ G` vanishes exactly when the corresponding
cohomology object of the `G`-image does.

All names are in the namespace `Stacks.CategoryTheory.CechComplex`.

## Main definitions

* `isLimitMapFan`: the `G`-image of the degree `n` term is the product of the `G`-images of the
  sections.
* `mapCoeff`: the degreewise comparison map.
* `mapCoeffIso`: the `G`-image of the Čech complex of `P` is isomorphic to the Čech complex of
  `P ⋙ G`, as cochain complexes.

## Main results

* `mapCoeff_comp_d`: the comparison commutes with the differentials.
* `isZero_homology_mapCoeff_iff`: a Čech cohomology object of `P ⋙ G` vanishes if and only if the
  corresponding cohomology object of the `G`-image of the Čech complex of `P` vanishes.

## Implementation notes

The hypothesis on `G` is `∀ J : Type w, PreservesLimitsOfShape (Discrete J) G`, which is what
`CategoryTheory.Limits.isLimitFanMkObjOfIsLimit` consumes at each of the index types
`Fin (n + 1) → ι`.

No `eqToHom` appears: both complexes are built by `lift` out of the universal property of the
degreewise products, and `(P ⋙ G).obj (op (inter U x))` is definitionally
`G.obj (P.obj (op (inter U x)))`.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' v'' u u' u''

namespace Stacks.CategoryTheory.CechComplex

section CoefficientChange

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type u''} [Category.{v''} B] [Preadditive B] [HasProducts.{w} B]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A) (G : A ⥤ B) [G.Additive]
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- **The `G`-image of the degree `n` term of a Čech complex is still a product.** Applying a
product-preserving functor to the degreewise description of
`Stacks.CategoryTheory.CechComplex.isLimitFan` leaves a limit fan. -/
noncomputable def isLimitMapFan (n : ℕ) :
    IsLimit (Fan.mk (G.obj (((cechComplexFunctor U).obj P).X n))
      fun x : Fin (n + 1) → ι ↦ G.map (π U P n x)) :=
  isLimitFanMkObjOfIsLimit G _ _ (isLimitFan U P n)

/-- The degree `n` comparison map from the `G`-image of the Čech complex of `P` to the Čech complex
of `P ⋙ G`, given on each factor by the `G`-image of the corresponding projection. -/
noncomputable def mapCoeff (n : ℕ) :
    G.obj (((cechComplexFunctor U).obj P).X n) ⟶
      ((cechComplexFunctor U).obj (P ⋙ G)).X n :=
  lift U (P ⋙ G) fun x ↦ G.map (π U P n x)

/-- The degree `n` comparison map in the other direction, obtained from the universal property of
`Stacks.CategoryTheory.CechComplex.isLimitMapFan`. -/
noncomputable def mapCoeffInv (n : ℕ) :
    ((cechComplexFunctor U).obj (P ⋙ G)).X n ⟶
      G.obj (((cechComplexFunctor U).obj P).X n) :=
  (isLimitMapFan U P G n).lift (Fan.mk _ (π U (P ⋙ G) n))

omit [G.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G] in
/-- The comparison map followed by the projection of the Čech complex of `P ⋙ G` onto the factor
indexed by `x` is the `G`-image of the projection of the Čech complex of `P` onto that factor. -/
@[reassoc (attr := simp)]
theorem mapCoeff_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    mapCoeff U P G n ≫ π U (P ⋙ G) n x = G.map (π U P n x) :=
  lift_comp_π U (P ⋙ G) _ x

omit [G.Additive] in
/-- The inverse comparison map followed by the `G`-image of the projection onto the factor indexed
by `x` is the projection of the Čech complex of `P ⋙ G` onto that factor. -/
@[reassoc (attr := simp)]
theorem mapCoeffInv_comp_map_π (n : ℕ) (x : Fin (n + 1) → ι) :
    mapCoeffInv U P G n ≫ G.map (π U P n x) = π U (P ⋙ G) n x :=
  (isLimitMapFan U P G n).fac (Fan.mk _ (π U (P ⋙ G) n)) ⟨x⟩

omit [G.Additive] in
/-- The comparison map followed by the inverse comparison map is the identity. -/
theorem mapCoeff_comp_mapCoeffInv (n : ℕ) :
    mapCoeff U P G n ≫ mapCoeffInv U P G n = 𝟙 _ :=
  (isLimitMapFan U P G n).hom_ext fun j ↦ by
    obtain ⟨x⟩ := j
    rw [Fan.mk_π_app, Category.assoc, mapCoeffInv_comp_map_π, mapCoeff_comp_π, Category.id_comp]

omit [G.Additive] in
/-- The inverse comparison map followed by the comparison map is the identity. -/
theorem mapCoeffInv_comp_mapCoeff (n : ℕ) :
    mapCoeffInv U P G n ≫ mapCoeff U P G n = 𝟙 _ :=
  hom_ext U (P ⋙ G) fun x ↦ by
    rw [Category.assoc, mapCoeff_comp_π, mapCoeffInv_comp_map_π, Category.id_comp]

omit [G.Additive] in
/-- The degree `n` comparison map is an isomorphism. -/
theorem isIso_mapCoeff (n : ℕ) : IsIso (mapCoeff U P G n) :=
  ⟨mapCoeffInv U P G n, mapCoeff_comp_mapCoeffInv U P G n, mapCoeffInv_comp_mapCoeff U P G n⟩

omit [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G] in
/-- **The comparison is a chain map.** The degreewise comparison maps commute with the
differentials of the two Čech complexes. -/
theorem mapCoeff_comp_d (n : ℕ) :
    mapCoeff U P G n ≫ ((cechComplexFunctor U).obj (P ⋙ G)).d n (n + 1) =
      G.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫ mapCoeff U P G (n + 1) :=
  hom_ext U (P ⋙ G) fun y ↦ by
    rw [Category.assoc, d_comp_π, Preadditive.comp_sum, Category.assoc, mapCoeff_comp_π,
      ← G.map_comp, d_comp_π, G.map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, ← Category.assoc, mapCoeff_comp_π, G.map_zsmul, G.map_comp]
    rfl

/-- The degreewise comparison maps, assembled into a morphism of cochain complexes. -/
noncomputable def mapCoeffHom :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ⟶
      (cechComplexFunctor U).obj (P ⋙ G) where
  f := mapCoeff U P G
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact mapCoeff_comp_d U P G i

/-- **The `G`-image of the Čech complex of `P` is the Čech complex of `P ⋙ G`.** For an additive
functor preserving the products occurring in the complex, changing the coefficient category
commutes with forming the Čech complex of a family. -/
noncomputable def mapCoeffIso :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ G) :=
  haveI (n : ℕ) : IsIso ((mapCoeffHom U P G).f n) := isIso_mapCoeff U P G n
  haveI := HomologicalComplex.Hom.isIso_of_components (mapCoeffHom U P G)
  asIso (mapCoeffHom U P G)

/-- The `n`-th Čech cohomology object of `P ⋙ G` vanishes if and only if the `n`-th cohomology
object of the `G`-image of the Čech complex of `P` vanishes. -/
theorem isZero_homology_mapCoeff_iff [CategoryWithHomology B] (n : ℕ) :
    IsZero (((cechComplexFunctor U).obj (P ⋙ G)).homology n) ↔
      IsZero ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor U).obj P))).homology n) :=
  (HomologicalComplex.homologyMapIso (mapCoeffIso U P G) n).isZero_iff.symm

end CoefficientChange

end Stacks.CategoryTheory.CechComplex

end
