module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# Assembling a degreewise comparison of Čech complexes into a comparison of complexes

Let `U₁ : ι → C₁` and `U₂ : ι → C₂` be two families indexed by the *same* type, let
`P₁ : C₁ᵒᵖ ⥤ A₁` and `P₂ : C₂ᵒᵖ ⥤ A₂` be presheaves, and let `G₁ : A₁ ⥤ B`, `G₂ : A₂ ⥤ B` be
additive functors into a common target. Suppose given, for every nonempty tuple
`x : Fin (m + 1) → ι`, an isomorphism

  `e x : G₁(P₁(inter U₁ x)) ≅ G₂(P₂(inter U₂ x))`

commuting with the reindexing maps `interMap`. This file assembles that family into an
isomorphism of cochain complexes

  `G₁(Čech(U₁, P₁)) ≅ G₂(Čech(U₂, P₂))`

in `CochainComplex B ℕ`, where `Čech` is Mathlib's `CategoryTheory.cechComplexFunctor` and
`G(-)` means `Functor.mapHomologicalComplex`.

This is the step that turns a *degreewise* comparison of Čech complexes into a comparison of
`CochainComplex` objects, which is what a homology functor can be applied to. The two inputs
it needs are exactly the two facts one proves about such a comparison: that it is an
isomorphism on each intersection, and that it commutes with restriction — the Čech
differential being an alternating sum of restrictions (`d_comp_π`).

## Main definitions

* `Stacks.CategoryTheory.CechComplex.isLimitFanMap`: the image under a product-preserving
  functor of the degree-`n` term of the Čech complex is again the product of the images of the
  sections over the intersections.
* `Stacks.CategoryTheory.CechComplex.cechComparisonHom` and `cechComparisonInv`: the two
  degreewise maps determined by the family `e`, and `cechComparisonIsoDeg` the isomorphism they
  constitute.
* `Stacks.CategoryTheory.CechComplex.cechComparisonIso`: **the isomorphism of cochain
  complexes.**
* `Stacks.CategoryTheory.CechComplex.cechComparisonIsoOfAdditive`: the same, with the two
  product-preservation hypotheses discharged from additivity of `G₁`, `G₂` and finiteness of
  the index type — the form a consumer normally wants.

## Main results

* `Stacks.CategoryTheory.CechComplex.cechComparisonHom_comp_π`: the degreewise comparison is
  characterised by its components, `cmp ≫ G₂(π x) = G₁(π x) ≫ e x`.
* `Stacks.CategoryTheory.CechComplex.cechComparisonHom_comm_d`: **the degreewise comparisons
  commute with the Čech differentials.**

## Implementation notes

Neither functor is asked to preserve all limits: the degree-`n` term of the Čech complex is a
product over `Fin (n + 1) → ι`, so finite products suffice when `ι` is finite, and an additive
functor preserves those. The two limit hypotheses are taken as explicit arguments
(`h₁`, `h₂`) rather than as instances, so that a consumer whose functor preserves the relevant
products for some other reason — flatness, say — can supply them directly;
`cechComparisonIsoOfAdditive` is the additive specialisation.

The isomorphism is built as an explicit pair of mutually inverse maps, each obtained as a lift
through the universal property of the *other* side's product, rather than by transporting one
limit cone along the family `e`. That keeps every step a `Fan`-level computation with
`IsLimit.fac` and `IsLimit.hom_ext`, and avoids forming any iso of diagrams.

The compatibility hypothesis `he` is stated for an arbitrary reindexing
`h : Fin (m' + 1) → Fin (m + 1)`, which is more than the differential uses: `d_comp_π` only
needs the face reindexings `Fin.succAbove`. Stating it for all `h` costs a consumer nothing,
since a restriction-compatible comparison is compatible with every reindexing, and it keeps the
hypothesis independent of the shape of the differential.

**Only nonempty tuples are asked for.** Both `e` and `he` are indexed by tuples
`Fin (m + 1) → ι`, never by the empty tuple, because the degree-`n` term of the Čech complex is
a product over `Fin (n + 1) → ι` and nothing below ever evaluates the family at `m = 0`. The
restriction matters: for a covering of a scheme by affine opens the comparison on an
intersection of members is affine base change, available exactly because a nonempty
intersection of affine opens is affine, whereas the empty intersection is the whole space and
the comparison there is the *conclusion* of the Čech argument rather than an input to it. A
family indexed by all of `Fin m → ι` would therefore be unsatisfiable in the intended
application.

The index type `ι` is shared between the two families. Geometrically this is the statement
that the second covering is indexed by the first — for a base change of a cover by its
preimage, which is the case this was written for, the preimages of the members are the members
of the preimage cover.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ vA vA' vB u₁ u₂ uA uA' uB

namespace Stacks.CategoryTheory.CechComplex

section Comparison

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {A₁ : Type uA} [Category.{vA} A₁] [Preadditive A₁] [HasProducts.{w} A₁]
  {A₂ : Type uA'} [Category.{vA'} A₂] [Preadditive A₂] [HasProducts.{w} A₂]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  [HasFiniteProducts C₁] [HasFiniteProducts C₂]
  {ι : Type w} (U₁ : ι → C₁) (U₂ : ι → C₂)
  (P₁ : C₁ᵒᵖ ⥤ A₁) (P₂ : C₂ᵒᵖ ⥤ A₂) (G₁ : A₁ ⥤ B) (G₂ : A₂ ⥤ B)

/-- **The degreewise description of the Čech complex, pushed along a functor.** If `G`
preserves the product over the tuples, then the image under `G` of the degree-`n` term of the
Čech complex of `U₁` is the product of the images of the sections over the intersections, with
the images of the Čech projections as its projections. -/
def isLimitFanMap (G : A₁ ⥤ B) (n : ℕ)
    [PreservesLimit (Discrete.functor (fun x : Fin (n + 1) → ι => P₁.obj (op (inter U₁ x)))) G] :
    IsLimit (Fan.mk (G.obj (((cechComplexFunctor U₁).obj P₁).X n))
      (fun x => G.map (π U₁ P₁ n x)) :
        Fan fun x : Fin (n + 1) → ι => G.obj (P₁.obj (op (inter U₁ x)))) :=
  isLimitFanMkObjOfIsLimit G _ _ (isLimitFan U₁ P₁ n)

variable (e : ∀ {m : ℕ} (x : Fin (m + 1) → ι),
    G₁.obj (P₁.obj (op (inter U₁ x))) ≅ G₂.obj (P₂.obj (op (inter U₂ x))))
  (h₁ : ∀ n : ℕ, IsLimit (Fan.mk (G₁.obj (((cechComplexFunctor U₁).obj P₁).X n))
      (fun x => G₁.map (π U₁ P₁ n x)) :
        Fan fun x : Fin (n + 1) → ι => G₁.obj (P₁.obj (op (inter U₁ x)))))
  (h₂ : ∀ n : ℕ, IsLimit (Fan.mk (G₂.obj (((cechComplexFunctor U₂).obj P₂).X n))
      (fun x => G₂.map (π U₂ P₂ n x)) :
        Fan fun x : Fin (n + 1) → ι => G₂.obj (P₂.obj (op (inter U₂ x)))))

/-- **The degreewise comparison of Čech complexes** determined by the family `e`: the map whose
component at a tuple `x` is `e x` applied after the `x`-th Čech projection. -/
def cechComparisonHom (n : ℕ) :
    G₁.obj (((cechComplexFunctor U₁).obj P₁).X n) ⟶
      G₂.obj (((cechComplexFunctor U₂).obj P₂).X n) :=
  (h₂ n).lift (Fan.mk (G₁.obj (((cechComplexFunctor U₁).obj P₁).X n))
    (fun x => G₁.map (π U₁ P₁ n x) ≫ (e x).hom))

/-- The degreewise comparison in the other direction, built from the inverses of the `e x`. -/
def cechComparisonInv (n : ℕ) :
    G₂.obj (((cechComplexFunctor U₂).obj P₂).X n) ⟶
      G₁.obj (((cechComplexFunctor U₁).obj P₁).X n) :=
  (h₁ n).lift (Fan.mk (G₂.obj (((cechComplexFunctor U₂).obj P₂).X n))
    (fun x => G₂.map (π U₂ P₂ n x) ≫ (e x).inv))

omit [Preadditive B] in
/-- **The components of the degreewise comparison.** -/
@[reassoc]
theorem cechComparisonHom_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ n ≫ G₂.map (π U₂ P₂ n x) =
      G₁.map (π U₁ P₁ n x) ≫ (e x).hom :=
  (h₂ n).fac _ ⟨x⟩

omit [Preadditive B] in
/-- The components of the comparison in the other direction. -/
@[reassoc]
theorem cechComparisonInv_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    cechComparisonInv U₁ U₂ P₁ P₂ G₁ G₂ e h₁ n ≫ G₁.map (π U₁ P₁ n x) =
      G₂.map (π U₂ P₂ n x) ≫ (e x).inv :=
  (h₁ n).fac _ ⟨x⟩

omit [Preadditive B] in
/-- `cechComparisonInv` is a left inverse of `cechComparisonHom`. -/
theorem cechComparisonHom_comp_inv (n : ℕ) :
    cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ n ≫
        cechComparisonInv U₁ U₂ P₁ P₂ G₁ G₂ e h₁ n = 𝟙 _ := by
  refine (h₁ n).hom_ext fun j => ?_
  obtain ⟨x⟩ := j
  rw [Category.assoc]
  simp only [Fan.mk_π_app]
  rw [cechComparisonInv_comp_π, cechComparisonHom_comp_π_assoc]
  simp

omit [Preadditive B] in
/-- `cechComparisonInv` is a right inverse of `cechComparisonHom`. -/
theorem cechComparisonInv_comp_hom (n : ℕ) :
    cechComparisonInv U₁ U₂ P₁ P₂ G₁ G₂ e h₁ n ≫
        cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ n = 𝟙 _ :=
  -- `cechComparisonInv` is `cechComparisonHom` for the swapped data and the inverse family
  cechComparisonHom_comp_inv U₂ U₁ P₂ P₁ G₂ G₁ (fun x => (e x).symm) h₂ h₁ n

/-- **The degreewise comparison is an isomorphism.** -/
def cechComparisonIsoDeg (n : ℕ) :
    G₁.obj (((cechComplexFunctor U₁).obj P₁).X n) ≅
      G₂.obj (((cechComplexFunctor U₂).obj P₂).X n) where
  hom := cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ n
  inv := cechComparisonInv U₁ U₂ P₁ P₂ G₁ G₂ e h₁ n
  hom_inv_id := cechComparisonHom_comp_inv U₁ U₂ P₁ P₂ G₁ G₂ e h₁ h₂ n
  inv_hom_id := cechComparisonInv_comp_hom U₁ U₂ P₁ P₂ G₁ G₂ e h₁ h₂ n

variable (he : ∀ {m m' : ℕ} (x : Fin (m + 1) → ι) (h : Fin (m' + 1) → Fin (m + 1)),
    (e (x ∘ h)).hom ≫ G₂.map (P₂.map (interMap U₂ x h).op) =
      G₁.map (P₁.map (interMap U₁ x h).op) ≫ (e x).hom)

include he in
/-- **The degreewise comparisons commute with the Čech differentials.** Both differentials are
the alternating sum of the restrictions along the face reindexings (`d_comp_π`), and the
comparison commutes with each of those by hypothesis. -/
theorem cechComparisonHom_comm_d [G₁.Additive] [G₂.Additive] (n : ℕ) :
    cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ n ≫
          G₂.map (((cechComplexFunctor U₂).obj P₂).d n (n + 1)) =
      G₁.map (((cechComplexFunctor U₁).obj P₁).d n (n + 1)) ≫
        cechComparisonHom U₁ U₂ P₁ P₂ G₁ G₂ e h₂ (n + 1) := by
  refine (h₂ (n + 1)).hom_ext fun j => ?_
  obtain ⟨y⟩ := j
  simp only [Fan.mk_π_app, Category.assoc]
  rw [← G₂.map_comp, d_comp_π, cechComparisonHom_comp_π, ← Category.assoc, ← G₁.map_comp,
    d_comp_π]
  rw [G₂.map_sum, G₁.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [G₂.map_zsmul, G₁.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z => ((-1 : ℤ) ^ (i : ℕ)) • z) ?_
  rw [G₂.map_comp, G₁.map_comp, ← Category.assoc, cechComparisonHom_comp_π, Category.assoc,
    Category.assoc, he y i.succAbove]

include he in
/-- **The comparison of Čech complexes.** A family of isomorphisms on the sections over the
intersections, compatible with the reindexing maps, assembles into an isomorphism of the two
Čech cochain complexes, pushed into the common target category. -/
def cechComparisonIso [G₁.Additive] [G₂.Additive] :
    (G₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U₁).obj P₁) ≅
      (G₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U₂).obj P₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => cechComparisonIsoDeg U₁ U₂ P₁ P₂ G₁ G₂ e h₁ h₂ n) (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact cechComparisonHom_comm_d U₁ U₂ P₁ P₂ G₁ G₂ e h₂ he i)

end Comparison

section Additive

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {A₁ : Type uA} [Category.{vA} A₁] [Preadditive A₁] [HasProducts.{w} A₁]
  {A₂ : Type uA'} [Category.{vA'} A₂] [Preadditive A₂] [HasProducts.{w} A₂]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  [HasFiniteProducts C₁] [HasFiniteProducts C₂]
  {ι : Type w} [Finite ι] (U₁ : ι → C₁) (U₂ : ι → C₂)
  (P₁ : C₁ᵒᵖ ⥤ A₁) (P₂ : C₂ᵒᵖ ⥤ A₂) (G₁ : A₁ ⥤ B) (G₂ : A₂ ⥤ B)
  [G₁.Additive] [G₂.Additive]

/-- **The comparison of Čech complexes, for additive functors and a finite index type.** This
is `cechComparisonIso` with its two product-preservation hypotheses discharged: the degree-`n`
term of a Čech complex is a product over `Fin (n + 1) → ι`, which is finite when `ι` is, and an
additive functor preserves finite products. -/
def cechComparisonIsoOfAdditive
    (e : ∀ {m : ℕ} (x : Fin (m + 1) → ι),
      G₁.obj (P₁.obj (op (inter U₁ x))) ≅ G₂.obj (P₂.obj (op (inter U₂ x))))
    (he : ∀ {m m' : ℕ} (x : Fin (m + 1) → ι) (h : Fin (m' + 1) → Fin (m + 1)),
      (e (x ∘ h)).hom ≫ G₂.map (P₂.map (interMap U₂ x h).op) =
        G₁.map (P₁.map (interMap U₁ x h).op) ≫ (e x).hom) :
    (G₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U₁).obj P₁) ≅
      (G₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U₂).obj P₂) :=
  cechComparisonIso U₁ U₂ P₁ P₂ G₁ G₂ e
    (fun n => isLimitFanMap U₁ P₁ G₁ n) (fun n => isLimitFanMap U₂ P₂ G₂ n) he

end Additive

end Stacks.CategoryTheory.CechComplex

end
