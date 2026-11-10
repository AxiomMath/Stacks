module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapToRepresentingSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram

/-!
# The local complete intersection locus in the relative finite Hilbert category

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S` and
let `d` be a natural number. An object `(U, Z, y, x, α)` of the relative finite Hilbert category
`ℋ_d(𝒳/𝒴)` determines, for every algebraic space `X_y` over `U` representing the 2-fibre product
`(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`, a morphism `x_α : Z ⟶ X_y` of algebraic spaces over `U`. The *local
complete intersection locus* `ℋ_{d,lci}(𝒳/𝒴)` is the full subcategory of `ℋ_d(𝒳/𝒴)` on the objects
for which `x_α` is unramified and a local complete intersection morphism.

The morphism `x_α` is the one of Stacks 06CK; the data exhibiting it — a scheme-valued point `y` of
`𝒴` over `U` through which the object `y` of the quintuple is read, a representing presheaf `X_y`,
an equivalence over the big fppf site of `U` exhibiting `X_y` as representing the 2-fibre product,
and the comparison isomorphism over `Z` — is packaged as
`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData`.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.coverOver`: the cover `Z` of an object of
  `ℋ_d(𝒳/𝒴)`, read as an object of the big fppf site of `U` through its structure morphism.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.baseOver` and
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.coverToBase`: the base `U` as the terminal object
  of its own big fppf site, and the structure morphism `q` read there.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData`: the data of a scheme-valued point of `𝒴`
  over `U` extending `y`, an algebraic space `X_y` representing the 2-fibre product of `F` with it,
  and a comparison isomorphism over `Z` matching `α`.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.map`: the morphism `x_α : Z ⟶ X_y` of
  algebraic spaces over `U` that such data names.
* `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus`: the objects of `ℋ_d(𝒳/𝒴)` whose relative map is
  unramified and a local complete intersection morphism.
* `AlgebraicGeometry.Stack.lciFiniteHilbertCategory`: the full subcategory `ℋ_{d,lci}(𝒳/𝒴)`,
  regarded as a category over the big fppf site.
* `AlgebraicGeometry.Stack.lciFiniteHilbertInclusion`: the inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)`.
* `AlgebraicGeometry.Stack.lciFiniteHilbertToTarget`: the 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` obtained
  by restricting the 1-morphism of Stacks 05WD to the locus.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.overMap_coverOver`: reading the cover over the base
  and then forgetting the base returns the cover.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.x_over_coverOver`: the object `x` of `𝒳` lies over
  the image of `Z` under the forgetful functor from the big fppf site of `U` to that of `S`.
* `AlgebraicGeometry.Stack.FiniteHilbert.isLocallyOfFiniteType_relativeMapData_map_of_lciLocus`:
  the relative map of an object of the locus is locally of finite type.

## References

* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 05VZ](https://stacks.math.columbia.edu/tag/05VZ)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-! ### The cover of a quintuple as an object over its base -/

/-- The cover `Z` of an object of `ℋ_d(𝒳/𝒴)`, read as an object of the big fppf site of its base
`U` through the structure morphism `q : Z ⟶ U`. -/
def Object.coverOver (P : Object B S hS 𝒳 𝒴 F d) : BigFppfOver B P.U.left.1 P.U.left.2 :=
  Over.mk P.q.left

/-- The base `U` of an object of `ℋ_d(𝒳/𝒴)`, read as the terminal object of the big fppf site of
`U`. -/
def Object.baseOver (P : Object B S hS 𝒳 𝒴 F d) : BigFppfOver B P.U.left.1 P.U.left.2 :=
  Over.mk (𝟙 P.U.left)

/-- The structure morphism `q : Z ⟶ U` of the cover of an object of `ℋ_d(𝒳/𝒴)`, read as a morphism
of the big fppf site of `U`. -/
def Object.coverToBase (P : Object B S hS 𝒳 𝒴 F d) : P.coverOver ⟶ P.baseOver :=
  Over.homMk P.q.left (by simp [Object.coverOver, Object.baseOver])

/-- Reading the cover of an object of `ℋ_d(𝒳/𝒴)` over its base and then forgetting the base returns
the cover. -/
theorem Object.overMap_coverOver (P : Object B S hS 𝒳 𝒴 F d) :
    (Over.map P.U.hom).obj P.coverOver = P.Z := by
  change Over.mk (P.q.left ≫ P.U.hom) = Over.mk P.Z.hom
  congr 1
  exact P.q.w

/-- The object `x` of `𝒳` of a quintuple lies over the image of the cover read as an object over
the base. -/
theorem Object.x_over_coverOver (P : Object B S hS 𝒳 𝒴 F d) :
    𝒳.toBasedCategory.p.obj P.x = (Over.map P.U.hom).obj P.coverOver :=
  P.x_over.trans P.overMap_coverOver.symm

/-! ### The data exhibiting the relative map -/

/-- The data exhibiting the relative map `x_α` of Stacks 06CK for an object `(U, Z, y, x, α)` of
`ℋ_d(𝒳/𝒴)`: a scheme-valued point `y` of `𝒴` over `U` together with a vertical morphism from its
value at `U` to the object `y` of the quintuple, an algebraic space `X_y` over `U` with an
equivalence exhibiting it as representing the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`, and
an isomorphism `α` of the restriction of the point to `Z` with `F x`, vertical over `Z` and
compatible with the identification of the quintuple. -/
structure RelativeMapData (P : Object B S hS 𝒳 𝒴 F d) where
  /-- The scheme-valued point of `𝒴` over the base of the quintuple. -/
  y : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj
  /-- The point is a section of `𝒴` over the big fppf site of `U`. -/
  y_comp : y ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom
  /-- The identification of the value of the point at `U` with the object `y` of the quintuple. -/
  yUnit : y.obj P.baseOver ⟶ P.y
  /-- That identification is vertical over `U`. -/
  yUnit_over : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) yUnit
  /-- The presheaf representing the 2-fibre product of `F` with the point. -/
  Xy : (BigFppfOver B P.U.left.1 P.U.left.2)ᵒᵖ ⥤ Type u
  /-- It is an algebraic space over `U`. -/
  isAlgebraicSpace : IsAlgebraicSpace B P.U.left.1 P.U.left.2 Xy
  /-- The equivalence over the big fppf site of `U` exhibiting `X_y` as representing the 2-fibre
  product. -/
  e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map P.U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
      F.toFunctor)
    (presheafOfCategories (Xy ⋙ typeToCat)).p
  /-- The comparison isomorphism of the restriction of the point to `Z` with `F x`. -/
  α : y.obj P.coverOver ≅ F.toFunctor.obj P.x
  /-- The comparison isomorphism is vertical over `Z`. -/
  α_over : 𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj P.coverOver)) α.hom
  /-- The comparison isomorphism recovers the identification of the quintuple. -/
  α_comp : α.inv ≫ y.map P.coverToBase ≫ yUnit = P.α

/-- The morphism `x_α : Z ⟶ X_y` of algebraic spaces over `U` named by data exhibiting the relative
map: the morphism of Stacks 06CK attached to the cover read over the base, the object `x` of `𝒳`
and the comparison isomorphism. -/
def RelativeMapData.map {P : Object B S hS 𝒳 𝒴 F d} (D : RelativeMapData P) :
    (⟨yoneda.obj P.coverOver,
        isAlgebraicSpace_yoneda B P.U.left.1 P.U.left.2 P.coverOver⟩ :
      AlgebraicSpaces B P.U.left.1 P.U.left.2) ⟶ ⟨D.Xy, D.isAlgebraicSpace⟩ :=
  relativeMap F D.y D.e D.isAlgebraicSpace P.coverOver P.x P.x_over_coverOver D.α D.α_over

/-! ### The locus -/

/-- The objects of the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` whose relative map
`x_α : Z ⟶ X_y` of Stacks 06CK is unramified and a local complete intersection morphism, for every
algebraic space representing the relevant 2-fibre product and every equivalence exhibiting it. -/
@[stacks 06CJ "the objects of ℋ_d(𝒳/𝒴) with unramified Koszul relative map"]
def lciLocus : ObjectProperty (Object B S hS 𝒳 𝒴 F d) :=
  fun P ↦ ∀ D : RelativeMapData P,
    Space.IsUnramified B P.U.left.1 P.U.left.2 D.map.hom ∧
      Space.IsLocalCompleteIntersection B P.U.left.1 P.U.left.2 D.map.hom

/-- The relative map of an object of the local complete intersection locus is locally of finite
type. -/
theorem isLocallyOfFiniteType_relativeMapData_map_of_lciLocus
    {P : Object B S hS 𝒳 𝒴 F d} (hP : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := d) P) (D : RelativeMapData P) :
    Space.IsLocallyOfFiniteType B P.U.left.1 P.U.left.2 D.map.hom :=
  Space.isLocallyOfFiniteType_of_isUnramified B P.U.left.1 P.U.left.2 (hP D).1

end FiniteHilbert

/-- The local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)`: the full subcategory of the relative
finite Hilbert category on the objects whose relative map is unramified and a local complete
intersection morphism, regarded as a category over the big fppf site through the restriction of the
canonical projection. -/
@[stacks 06CJ "the full subcategory ℋ_{d,lci}(𝒳/𝒴) of ℋ_d(𝒳/𝒴)"]
noncomputable def lciFiniteHilbertCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    ((FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).ι ⋙
      finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` of the local complete intersection locus into the
relative finite Hilbert category, as a 1-morphism of categories over the big fppf site. -/
@[stacks 06CJ "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)"]
def lciFiniteHilbertInclusion :
    lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) where
  toFunctor := (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
    (d := d)).ι
  w := rfl

/-- The 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` to the target stack: the 1-morphism of Stacks 05WD
restricted along the inclusion of the local complete intersection locus. -/
noncomputable def lciFiniteHilbertToTarget :
    lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      𝒴.toBasedCategory :=
  BasedFunctor.comp
    (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    (forgetTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

end AlgebraicGeometry.Stack

end
