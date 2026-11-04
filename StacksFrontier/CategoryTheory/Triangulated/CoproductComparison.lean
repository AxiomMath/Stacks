module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# The direct-sum comparison morphism of an exact functor of triangulated categories

Let `R : C ⥤ D` be an additive functor between pre-triangulated categories commuting with the
shift, and let `X` be a family of objects of `C` indexed by a type `J`. Whether `R` commutes
with the direct sum of that family is the invertibility of the canonical comparison morphism

`∐ᵢ R Xᵢ ⟶ R (∐ᵢ Xᵢ)`,

Mathlib's `CategoryTheory.Limits.sigmaComparison`. This file assembles the triangulated
two-out-of-three principle for that morphism: given a family of distinguished triangles
`Xᵢ ⟶ Yᵢ ⟶ Zᵢ ⟶ Xᵢ⟦1⟧`, if the comparison morphisms at the families `X` and `Z` are invertible
then so is the one at `Y`.

The ingredients are the coproduct of a family of distinguished triangles, which is distinguished
([Stacks, Tag 0CRG] part (2)(b), available as the omnibus statement
`shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished` in the
`CategoryTheory.Pretriangulated` namespace),
and the morphism of distinguished triangles whose three components are the comparison morphisms
at the three families of vertices; the conclusion is then Mathlib's triangulated five lemma
`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃`.

## Main definitions

* `CategoryTheory.Pretriangulated.coproductTriangle` is the coproduct of a family of triangles.
* `CategoryTheory.Pretriangulated.coproductMapTriangle` is the coproduct of the images under `R`
  of a family of triangles.
* `CategoryTheory.Pretriangulated.coproductMapTriangleHom` is the morphism of triangles
  `coproductMapTriangle R T ⟶ R.mapTriangle.obj (coproductTriangle T)` whose components are the
  direct-sum comparison morphisms at the three families of vertices.

## Main results

* `CategoryTheory.Limits.sigmaComparison_naturality`: the comparison morphism is natural in the
  family.
* `CategoryTheory.Limits.sigmaComparison_comp`: the comparison morphism of a composite of two
  functors factors as the comparison morphism of the second at the image family followed by the
  image of the comparison morphism of the first, and
  `CategoryTheory.Limits.isIso_sigmaComparison_of_isIso_comp` reads that factorisation as a
  criterion for invertibility of the comparison morphism of the first factor.
* `CategoryTheory.Pretriangulated.coproductTriangle_distinguished` and
  `CategoryTheory.Pretriangulated.coproductMapTriangle_mem_distTriang`: a coproduct of
  distinguished triangles, respectively of their images under an exact functor, is
  distinguished.
* `CategoryTheory.Pretriangulated.isIso_sigmaComparison_of_distTriang`: **two out of three for
  the direct-sum comparison morphism.**
* `CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_isIso_sigmaComparison`: a functor
  whose direct-sum comparison morphisms are all invertible preserves direct sums.

## Implementation notes

The coproduct of a family of triangles is spelled out with `Triangle.mk` rather than through an
analogue of Mathlib's `CategoryTheory.Pretriangulated.productTriangle`, which does not exist;
the outer morphism carries no sign, exactly as in the statement of [Stacks, Tag 0CRG].

Two spellings of the vertices of the image triangles are in play: the family
`fun j ↦ (R.mapTriangle.obj (T j)).obj₁` that `coproductTriangle` produces when applied to the
images, and the family `fun j ↦ R.obj ((T j).obj₁)` that `sigmaComparison` produces. They are
definitionally equal, so `exact` crosses between them, but a `rw` does not: the comparison of the
two requires unfolding `CategoryTheory.Pretriangulated.Triangle.mk`, which happens at the default
transparency and not at the `implicit` transparency a rewrite re-typechecks at.
`CategoryTheory.Pretriangulated.coproductMapTriangle` is therefore written out in the second
spelling, so that every rewrite inside its theory stays on one side of that junction, and
`CategoryTheory.Pretriangulated.coproductMapTriangle_eq` records that it is the first spelling.

For the same reason the component equation of the third commutation square is isolated as
`CategoryTheory.Pretriangulated.coproductMapTriangleHom_comm₃_app`, stated entirely in terms of
`CategoryTheory.Limits.Sigma.desc` and `CategoryTheory.Functor.commShiftIso` rather than of the
projections of the mapped triangle.

## References

* [Stacks Project, Tag 0CRG](https://stacks.math.columbia.edu/tag/0CRG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u' v'' u''

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (R : C ⥤ D) {J : Type w}

/-- **The direct-sum comparison morphism is natural in the family.** For a family of morphisms
`φ j : X j ⟶ Y j`, the comparison morphisms at `X` and at `Y` intertwine the direct sum of the
images of the `φ j` with the image of their direct sum. -/
theorem sigmaComparison_naturality {X Y : J → C} (φ : ∀ j, X j ⟶ Y j)
    [HasCoproduct X] [HasCoproduct Y] [HasCoproduct fun j ↦ R.obj (X j)]
    [HasCoproduct fun j ↦ R.obj (Y j)] :
    (Limits.Sigma.map fun j ↦ R.map (φ j)) ≫ sigmaComparison R Y
      = sigmaComparison R X ≫ R.map (Limits.Sigma.map φ) := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc]
  rw [← R.map_comp, ← R.map_comp, Limits.Sigma.ι_map]

/-- An invertible direct-sum comparison morphism at a family `X` says that the functor preserves
the colimit of the discrete diagram on `X`; this is Mathlib's
`CategoryTheory.Limits.PreservesCoproduct.of_iso_comparison` with the invertibility taken as an
argument rather than as an instance. -/
theorem preservesColimit_discreteFunctor_of_isIso_sigmaComparison
    (X : J → C) [HasCoproduct X] [HasCoproduct fun j ↦ R.obj (X j)]
    (h : IsIso (sigmaComparison R X)) :
    PreservesColimit (Discrete.functor X) R :=
  have := h
  PreservesCoproduct.of_iso_comparison R X

/-- A functor preserving the colimit of a discrete diagram has an invertible direct-sum
comparison morphism at that family; this is the converse of
`CategoryTheory.Limits.preservesColimit_discreteFunctor_of_isIso_sigmaComparison`, with the
preservation taken as an argument rather than as an instance. -/
theorem isIso_sigmaComparison_of_preservesColimit
    (X : J → C) [HasCoproduct X] [HasCoproduct fun j ↦ R.obj (X j)]
    (h : PreservesColimit (Discrete.functor X) R) :
    IsIso (sigmaComparison R X) :=
  have := h
  inferInstance

/-- A functor all of whose `J`-indexed direct-sum comparison morphisms are invertible preserves
`J`-indexed direct sums. Every diagram of shape `Discrete J` is isomorphic to one of the form
`CategoryTheory.Discrete.functor`, where invertibility of the comparison morphism is the
hypothesis. -/
theorem preservesColimitsOfShape_discrete_of_isIso_sigmaComparison
    [HasCoproductsOfShape J C] [HasCoproductsOfShape J D]
    (h : ∀ X : J → C, IsIso (sigmaComparison R X)) :
    PreservesColimitsOfShape (Discrete J) R where
  preservesColimit {K} :=
    have := preservesColimit_discreteFunctor_of_isIso_sigmaComparison R
      (K.obj ∘ Discrete.mk) (h _)
    preservesColimit_of_iso_diagram R (Discrete.natIsoFunctor (F := K)).symm

/-! ### The comparison morphism of a composite -/

section Comp

variable {E : Type u''} [Category.{v''} E] (S : D ⥤ E)

/-- The images under a composite of two functors of a family with a direct sum have a direct sum
as soon as the iterated images do; the two families are definitionally equal, and this instance
is what lets `CategoryTheory.Limits.sigmaComparison` be formed at the composite. -/
instance hasCoproduct_comp_obj (X : J → C) [HasCoproduct fun j ↦ S.obj (R.obj (X j))] :
    HasCoproduct fun j ↦ (R ⋙ S).obj (X j) :=
  inferInstanceAs (HasCoproduct fun j ↦ S.obj (R.obj (X j)))

/-- **The direct-sum comparison morphism of a composite** is the comparison morphism of the
second functor at the family of images, followed by the image under the second functor of the
comparison morphism of the first. -/
theorem sigmaComparison_comp (X : J → C) [HasCoproduct X]
    [HasCoproduct fun j ↦ R.obj (X j)] [HasCoproduct fun j ↦ S.obj (R.obj (X j))] :
    sigmaComparison (R ⋙ S) X
      = sigmaComparison S (fun j ↦ R.obj (X j)) ≫ S.map (sigmaComparison R X) := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  refine (ι_comp_sigmaComparison (R ⋙ S) X j).trans ?_
  calc (R ⋙ S).map (Sigma.ι X j)
      = S.map (Sigma.ι (fun b ↦ R.obj (X b)) j ≫ sigmaComparison R X) :=
        (congrArg S.map (ι_comp_sigmaComparison R X j)).symm
    _ = S.map (Sigma.ι (fun b ↦ R.obj (X b)) j) ≫ S.map (sigmaComparison R X) := S.map_comp _ _
    _ = (Sigma.ι (fun b ↦ S.obj (R.obj (X b))) j ≫ sigmaComparison S (fun b ↦ R.obj (X b)))
          ≫ S.map (sigmaComparison R X) := by rw [ι_comp_sigmaComparison]
    _ = Sigma.ι (fun b ↦ S.obj (R.obj (X b))) j ≫
          sigmaComparison S (fun b ↦ R.obj (X b)) ≫ S.map (sigmaComparison R X) :=
        Category.assoc _ _ _

/-- **The image under the second factor of the comparison morphism of the first** is invertible
as soon as the comparison morphisms of `R ⋙ S` and of `S` at the family of images are. -/
theorem isIso_map_sigmaComparison_of_isIso_comp (X : J → C) [HasCoproduct X]
    [HasCoproduct fun j ↦ R.obj (X j)] [HasCoproduct fun j ↦ S.obj (R.obj (X j))]
    (h : IsIso (sigmaComparison (R ⋙ S) X))
    (hS : IsIso (sigmaComparison S fun j ↦ R.obj (X j))) :
    IsIso (S.map (sigmaComparison R X)) := by
  have := hS
  have : IsIso ((sigmaComparison S fun j ↦ R.obj (X j)) ≫ S.map (sigmaComparison R X)) := by
    rwa [← sigmaComparison_comp R S X]
  exact IsIso.of_isIso_comp_left (sigmaComparison S fun j ↦ R.obj (X j)) _

/-- **Invertibility of the comparison morphism of the first factor of a composite.** If the
comparison morphisms of `R ⋙ S` and of `S` at the family of images are invertible and `S`
reflects isomorphisms, then the comparison morphism of `R` is invertible.

That `S` reflects isomorphisms is an explicit hypothesis rather than an instance: the categories
this is applied to come in definitionally equal but syntactically distinct spellings, across
which instance search does not pass, while an explicit argument is checked up to definitional
equality. -/
theorem isIso_sigmaComparison_of_isIso_comp (X : J → C) [HasCoproduct X]
    [HasCoproduct fun j ↦ R.obj (X j)] [HasCoproduct fun j ↦ S.obj (R.obj (X j))]
    (hrefl : S.ReflectsIsomorphisms) (h : IsIso (sigmaComparison (R ⋙ S) X))
    (hS : IsIso (sigmaComparison S fun j ↦ R.obj (X j))) :
    IsIso (sigmaComparison R X) := by
  have := hrefl
  have : IsIso (S.map (sigmaComparison R X)) :=
    isIso_map_sigmaComparison_of_isIso_comp R S X h hS
  exact isIso_of_reflects_iso _ S

end Comp

end CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

/-! ### The coproduct of a family of triangles -/

section Coproduct

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] {J : Type w} (T : J → Triangle C)
  [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃]

/-- **The coproduct of a family of triangles**: the triangle
`∐ Xᵢ ⟶ ∐ Yᵢ ⟶ ∐ Zᵢ ⟶ (∐ Xᵢ)⟦1⟧` whose first two morphisms are the direct sums of the given
ones and whose third is induced by them and the coprojections. -/
def coproductTriangle : Triangle C :=
  Triangle.mk (Limits.Sigma.map fun j ↦ (T j).mor₁) (Limits.Sigma.map fun j ↦ (T j).mor₂)
    (Sigma.desc fun j ↦ (T j).mor₃ ≫ (Sigma.ι (fun j ↦ (T j).obj₁) j)⟦(1 : ℤ)⟧')

end Coproduct

section Distinguished

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {J : Type w} (T : J → Triangle C)
  [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃]

/-- **A coproduct of distinguished triangles is distinguished**, which is [Stacks, Tag 0CRG]
part (2)(b), here for the triangle named by
`CategoryTheory.Pretriangulated.coproductTriangle`. -/
theorem coproductTriangle_distinguished (hT : ∀ j, T j ∈ distTriang C) :
    coproductTriangle T ∈ distTriang C :=
  (shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished
    (C := C) J).2.2.2 T hT

end Distinguished

/-! ### The comparison morphism of triangles -/

section Comparison

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] {D : Type u'} [Category.{v'} D]
  [HasShift D ℤ] (R : C ⥤ D) {J : Type w}

omit [HasShift C ℤ] in
/-- The shift of a coprojection followed by the shift of a direct-sum comparison morphism is the
shift of the image of that coprojection. -/
theorem shift_ι_comp_shift_sigmaComparison (X : J → C) [HasCoproduct X]
    [HasCoproduct fun j ↦ R.obj (X j)] (j : J) (n : ℤ) :
    (Sigma.ι (fun j ↦ R.obj (X j)) j)⟦n⟧' ≫ (sigmaComparison R X)⟦n⟧'
      = (R.map (Sigma.ι X j))⟦n⟧' :=
  ((CategoryTheory.shiftFunctor D n).map_comp _ _).symm.trans
    (congrArg (fun u ↦ (CategoryTheory.shiftFunctor D n).map u) (ι_comp_sigmaComparison R X j))

variable [R.CommShift ℤ] (T : J → Triangle C)
  [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃]
  [HasCoproduct fun j ↦ R.obj ((T j).obj₁)] [HasCoproduct fun j ↦ R.obj ((T j).obj₂)]
  [HasCoproduct fun j ↦ R.obj ((T j).obj₃)]

/-- The first vertices of the images of a family of triangles have a direct sum. -/
instance hasCoproduct_mapTriangle_obj₁ :
    HasCoproduct fun j ↦ (R.mapTriangle.obj (T j)).obj₁ :=
  inferInstanceAs (HasCoproduct fun j ↦ R.obj ((T j).obj₁))

/-- The second vertices of the images of a family of triangles have a direct sum. -/
instance hasCoproduct_mapTriangle_obj₂ :
    HasCoproduct fun j ↦ (R.mapTriangle.obj (T j)).obj₂ :=
  inferInstanceAs (HasCoproduct fun j ↦ R.obj ((T j).obj₂))

/-- The third vertices of the images of a family of triangles have a direct sum. -/
instance hasCoproduct_mapTriangle_obj₃ :
    HasCoproduct fun j ↦ (R.mapTriangle.obj (T j)).obj₃ :=
  inferInstanceAs (HasCoproduct fun j ↦ R.obj ((T j).obj₃))

/-- The third morphism of the image of a triangle under a functor commuting with the shift:
the image of the third morphism, followed by the shift-commutation isomorphism. -/
theorem mapTriangle_obj_mor₃ (X : Triangle C) :
    (R.mapTriangle.obj X).mor₃
      = R.map X.mor₃ ≫ (R.commShiftIso (1 : ℤ)).hom.app X.obj₁ := rfl

/-- **The coproduct of the images under `R` of a family of triangles.** This is
`CategoryTheory.Pretriangulated.coproductTriangle` of the family of image triangles, written out
with the vertices spelled as the images `R Xᵢ` of the vertices. -/
def coproductMapTriangle : Triangle D :=
  Triangle.mk (Limits.Sigma.map fun j ↦ R.map ((T j).mor₁))
    (Limits.Sigma.map fun j ↦ R.map ((T j).mor₂))
    (Sigma.desc fun j ↦ (R.map ((T j).mor₃) ≫ (R.commShiftIso (1 : ℤ)).hom.app ((T j).obj₁)) ≫
      (Sigma.ι (fun j ↦ R.obj ((T j).obj₁)) j)⟦(1 : ℤ)⟧')

omit [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃] in
/-- `CategoryTheory.Pretriangulated.coproductMapTriangle` is the coproduct of the family of
image triangles. -/
theorem coproductMapTriangle_eq :
    coproductMapTriangle R T = coproductTriangle fun j ↦ R.mapTriangle.obj (T j) := rfl

omit [HasCoproduct fun j ↦ (T j).obj₂] [HasCoproduct fun j ↦ R.obj ((T j).obj₂)] in
/-- The `j`-th component of the compatibility of the direct-sum comparison morphisms with the
third morphisms of the triangles. -/
theorem coproductMapTriangleHom_comm₃_app (j : J) :
    ((R.map ((T j).mor₃) ≫ (R.commShiftIso (1 : ℤ)).hom.app ((T j).obj₁)) ≫
        (Sigma.ι (fun j ↦ R.obj ((T j).obj₁)) j)⟦(1 : ℤ)⟧') ≫
          (sigmaComparison R fun j ↦ (T j).obj₁)⟦(1 : ℤ)⟧'
      = Sigma.ι (fun j ↦ R.obj ((T j).obj₃)) j ≫
          (sigmaComparison R fun j ↦ (T j).obj₃) ≫
            R.map (Sigma.desc fun j ↦ (T j).mor₃ ≫ (Sigma.ι (fun j ↦ (T j).obj₁) j)⟦(1 : ℤ)⟧') ≫
              (R.commShiftIso (1 : ℤ)).hom.app (∐ fun j ↦ (T j).obj₁) := by
  rw [Category.assoc, shift_ι_comp_shift_sigmaComparison, ι_comp_sigmaComparison_assoc,
    ← R.map_comp_assoc, Sigma.ι_desc, R.map_comp]
  simp only [Category.assoc]
  rw [R.commShiftIso_hom_naturality]

/-- **The comparison morphism of triangles**, from the coproduct of the images of a family of
triangles to the image of their coproduct, whose three components are the direct-sum comparison
morphisms at the three families of vertices. -/
def coproductMapTriangleHom :
    coproductMapTriangle R T ⟶ R.mapTriangle.obj (coproductTriangle T) :=
  Triangle.homMk _ _ (sigmaComparison R fun j ↦ (T j).obj₁)
    (sigmaComparison R fun j ↦ (T j).obj₂) (sigmaComparison R fun j ↦ (T j).obj₃)
    (sigmaComparison_naturality R fun j ↦ (T j).mor₁)
    (sigmaComparison_naturality R fun j ↦ (T j).mor₂)
    (by
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      change Sigma.ι (fun j ↦ R.obj ((T j).obj₃)) j ≫
          (Sigma.desc fun j ↦ (R.map ((T j).mor₃) ≫
            (R.commShiftIso (1 : ℤ)).hom.app ((T j).obj₁)) ≫
              (Sigma.ι (fun j ↦ R.obj ((T j).obj₁)) j)⟦(1 : ℤ)⟧') ≫
            (sigmaComparison R fun j ↦ (T j).obj₁)⟦(1 : ℤ)⟧'
        = Sigma.ι (fun j ↦ R.obj ((T j).obj₃)) j ≫
          (sigmaComparison R fun j ↦ (T j).obj₃) ≫
            R.map (Sigma.desc fun j ↦ (T j).mor₃ ≫
              (Sigma.ι (fun j ↦ (T j).obj₁) j)⟦(1 : ℤ)⟧') ≫
              (R.commShiftIso (1 : ℤ)).hom.app (∐ fun j ↦ (T j).obj₁)
      rw [← Category.assoc, Sigma.ι_desc]
      exact coproductMapTriangleHom_comm₃_app R T j)

omit [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃] in
/-- **A coproduct of the images of distinguished triangles under an exact functor is
distinguished.** -/
theorem coproductMapTriangle_mem_distTriang [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
    [R.IsTriangulated] (hT : ∀ j, T j ∈ distTriang C) :
    coproductMapTriangle R T ∈ distTriang D :=
  coproductTriangle_distinguished (fun j ↦ R.mapTriangle.obj (T j))
    fun j ↦ R.map_distinguished _ (hT j)

/-- **Two out of three for the direct-sum comparison morphism**, for a family of distinguished
triangles: if the comparison morphisms at the first and third families of vertices are
invertible, so is the one at the second.

The two triangles are the coproduct of the images and the image of the coproduct, both
distinguished, and the comparison morphisms are the three components of a morphism between them;
the conclusion is the triangulated five lemma. -/
theorem isIso_sigmaComparison_hom₂ [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
    [R.IsTriangulated] (hT : ∀ j, T j ∈ distTriang C)
    (h₁ : IsIso (sigmaComparison R fun j ↦ (T j).obj₁))
    (h₃ : IsIso (sigmaComparison R fun j ↦ (T j).obj₃)) :
    IsIso (sigmaComparison R fun j ↦ (T j).obj₂) :=
  isIso₂_of_isIso₁₃ (coproductMapTriangleHom R T)
    (coproductMapTriangle_mem_distTriang R T hT)
    (R.map_distinguished _ (coproductTriangle_distinguished T hT)) h₁ h₃

end Comparison

section Families

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  (R : C ⥤ D) [R.CommShift ℤ] [R.IsTriangulated] {J : Type w}

/-- **Two out of three for the direct-sum comparison morphism**, with the three families of
vertices and the three families of morphisms given separately. This is the form in which the
principle is applied: the triangles are produced one vertex family at a time, for instance from
the canonical truncation of a t-structure. -/
theorem isIso_sigmaComparison_of_distTriang {X Y Z : J → C}
    [HasCoproduct X] [HasCoproduct Y] [HasCoproduct Z]
    [HasCoproduct fun j ↦ R.obj (X j)] [HasCoproduct fun j ↦ R.obj (Y j)]
    [HasCoproduct fun j ↦ R.obj (Z j)]
    (f : ∀ j, X j ⟶ Y j) (g : ∀ j, Y j ⟶ Z j) (h : ∀ j, Z j ⟶ (X j)⟦(1 : ℤ)⟧)
    (hT : ∀ j, Triangle.mk (f j) (g j) (h j) ∈ distTriang C)
    (h₁ : IsIso (sigmaComparison R X)) (h₃ : IsIso (sigmaComparison R Z)) :
    IsIso (sigmaComparison R Y) := by
  let i₁ : HasCoproduct fun j ↦ (Triangle.mk (f j) (g j) (h j)).obj₁ :=
    inferInstanceAs (HasCoproduct X)
  let i₂ : HasCoproduct fun j ↦ (Triangle.mk (f j) (g j) (h j)).obj₂ :=
    inferInstanceAs (HasCoproduct Y)
  let i₃ : HasCoproduct fun j ↦ (Triangle.mk (f j) (g j) (h j)).obj₃ :=
    inferInstanceAs (HasCoproduct Z)
  let j₁ : HasCoproduct fun j ↦ R.obj ((Triangle.mk (f j) (g j) (h j)).obj₁) :=
    inferInstanceAs (HasCoproduct fun j ↦ R.obj (X j))
  let j₂ : HasCoproduct fun j ↦ R.obj ((Triangle.mk (f j) (g j) (h j)).obj₂) :=
    inferInstanceAs (HasCoproduct fun j ↦ R.obj (Y j))
  let j₃ : HasCoproduct fun j ↦ R.obj ((Triangle.mk (f j) (g j) (h j)).obj₃) :=
    inferInstanceAs (HasCoproduct fun j ↦ R.obj (Z j))
  exact isIso_sigmaComparison_hom₂ R (fun j ↦ Triangle.mk (f j) (g j) (h j)) hT h₁ h₃

end Families

end CategoryTheory.Pretriangulated

end
