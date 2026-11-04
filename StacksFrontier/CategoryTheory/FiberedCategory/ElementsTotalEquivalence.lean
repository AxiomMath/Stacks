module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Grp
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsTotalPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Presheaves on a category of elements are presheaves over `Z`

Let `C` be a category and let `Z` be a presheaf of sets on `C`. The total-presheaf construction
`CategoryTheory.PresheafOfCategories.elementsTotalPresheaf` sends a presheaf `F` on the category
of elements `El Z` of `Z` (Stacks 02XV applied to `Z ⋙ typeToCat`) to the presheaf `Σ_Z F` on `C`
whose sections over `V` are the pairs `(z ∈ Z(V), s ∈ F(V, z))`, together with its structure
morphism to `Z`. This file turns that construction into an **equivalence of categories**

```text
PSh(El Z) ≌ Over Z,
```

the inverse direction sending an object `X ⟶ Z` of the slice to its presheaf of fibres
`(V, z) ↦ {s ∈ X(V) | X(V) → Z(V) sends s to z}`, and records that the equivalence is one of
*cartesian monoidal* categories: it preserves finite products, so it carries group objects of
`PSh(El Z)` — presheaves of groups on the category of elements of `Z` — to group objects of
`CategoryTheory.Over Z`, where the tensor product is the fibre product over `Z`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.elementsTotalFunctor`: the total presheaf together with
  its structure morphism, as a functor `PSh(El Z) ⥤ Over Z`.
* `CategoryTheory.PresheafOfCategories.elementsFibrePresheaf`: the presheaf of fibres of an
  object over `Z`, as a functor `Over Z ⥤ PSh(El Z)`.
* `CategoryTheory.PresheafOfCategories.elementsTotalEquivalence`: the two are an equivalence of
  categories.
* `CategoryTheory.PresheafOfCategories.elementsTotalFunctorMonoidal` and
  `CategoryTheory.PresheafOfCategories.elementsFibrePresheafMonoidal`: the two functors are
  monoidal for the cartesian monoidal structures.

## Main results

* `CategoryTheory.PresheafOfCategories.totalFibreEquiv`: the fibre of `Σ_Z F` over a point `z` of
  `Z` is the value of `F` at `z`. This is the unit of the equivalence.
* `CategoryTheory.PresheafOfCategories.elementsTotalGrpEquivalence`: group objects of presheaves
  on the category of elements of `Z` are group objects over `Z`.

## Implementation notes

The presheaf of fibres is `CategoryTheory.PresheafOfCategories.fibrePresheaf`, the subpresheaf
`{g | θ g = s}` of a presheaf cut out by a morphism `θ` and a global section `s`, taken on the
category of elements of `Z` itself: `θ` is the structure morphism of `X` pulled back along the
projection of `El Z`, and `s` is the point of `Z` that an object of `El Z` names
(`CategoryTheory.PresheafOfCategories.elementsSection`), whose compatibility with restriction is
exactly the fibre condition in a morphism of `El Z`. Writing it this way keeps the identity and
the composition of `El Z` out of the functoriality proofs: `fibrePresheaf` is functorial already,
and the only place where a morphism of `El Z` is taken apart is
`CategoryTheory.PresheafOfCategories.elementsSection_naturality`.
`CategoryTheory.PresheafOfCategories.fibreAt` names the value of that subpresheaf so that its
elements can be built and taken apart by type ascription; `fibrePresheaf` is not reducible, so
anonymous-constructor notation does not see through it.

The equivalence is produced by `CategoryTheory.Equivalence.mk`, which adjointifies the unit, so
`elementsTotalEquivalence`'s unit is not `elementsTotalUnitIso` on the nose; what the consumers
need is that its *functor* is `elementsTotalFunctor`, which is true by construction.

That the two functors are monoidal is `CategoryTheory.Functor.Monoidal.ofChosenFiniteProducts`
applied to an equivalence, which preserves all limits. It is a `def` and not an instance in
Mathlib — making it one would create a diamond on identities and composites — which is why the
two monoidal structures here are `def`s as well, to be turned on with `letI` where a group object
is carried across.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] (Z : Cᵒᵖ ⥤ Type v)

/-! ### The presheaf of fibres of an object over `Z` -/

/-- The point of `Z` that an object of the category of elements of `Z` names, read as a global
section of the pullback of `Z` along the projection of that category. -/
abbrev elementsSection (a : (presheafOfCategories (Z ⋙ typeToCat)).obj) :
    ((discreteProjection Z).op ⋙ Z).obj (op a) :=
  a.fiber.as

/-- Those points are compatible with restriction: a morphism of the category of elements of `Z`
carries the point of `Z` its target names to the point its source names. -/
lemma elementsSection_naturality {a b : (presheafOfCategories (Z ⋙ typeToCat)).obj}
    (h : a ⟶ b) :
    ((discreteProjection Z).op ⋙ Z).map h.op (elementsSection Z b) = elementsSection Z a :=
  (Discrete.eq_of_hom h.fiber).symm

/-- The sections of an object `X` over `Z` that lie over a given point of `Z`. -/
abbrev fibreAt (X : Over Z) (a : (presheafOfCategories (Z ⋙ typeToCat)).obj) : Type v :=
  {s : X.left.obj (op a.base) // X.hom.app (op a.base) s = a.fiber.as}

/-- **The presheaf of fibres of an object over `Z`.** The presheaf on the category of elements of
`Z` whose sections at a point `(V, z)` are the sections of `X` over `V` that the structure
morphism of `X` sends to `z`. -/
abbrev elementsFibrePresheafObj (X : Over Z) :
    ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v :=
  fibrePresheaf (Functor.whiskerLeft (discreteProjection Z).op X.hom) (elementsSection Z)
    (elementsSection_naturality Z)

/-- The presheaf of fibres, as a functor on the slice over `Z`: a morphism over `Z` carries a
section lying over a point of `Z` to a section lying over the same point. -/
def elementsFibrePresheaf :
    Over Z ⥤ (((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) where
  obj X := elementsFibrePresheafObj Z X
  map {X Y} g :=
    { app a := ↾fun (s : fibreAt Z X a.unop) => (⟨g.left.app (op a.unop.base) s.1,
        (congrArg (fun t : X.left ⟶ Z => t.app (op a.unop.base) s.1) g.w).trans s.2⟩ :
        fibreAt Z Y a.unop)
      naturality a b h := by
        ext (s : fibreAt Z X a.unop)
        refine Subtype.ext ?_
        exact NatTrans.naturality_apply g.left ((discreteProjection Z).map h.unop).op s.1 }
  map_id X := by ext a (s : fibreAt Z X a.unop); rfl
  map_comp f g := by ext a s; rfl

/-! ### The total presheaf as a functor to the slice over `Z` -/

/-- **The total presheaf as a functor to the slice over `Z`.** A presheaf `F` on the category of
elements of `Z` goes to `Σ_Z F` together with its structure morphism to `Z`, and a morphism of
presheaves on the category of elements of `Z` acts on the second component of a section. -/
@[sga "4 I 5.11"]
def elementsTotalFunctor :
    (((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) ⥤ Over Z where
  obj F := Over.mk (elementsTotalProj Z F)
  map {F G} α := Over.homMk
    { app V := ↾fun p => ⟨p.1, α.app _ p.2⟩
      naturality U V f := by
        ext p
        exact congrArg (fun s => (⟨Z.map f p.1, s⟩ :
          (elementsTotalPresheaf Z G).obj V)) (α.naturality_apply _ p.2) } rfl
  map_id F := by ext V p; rfl
  map_comp α β := by ext V p; rfl

/-- The underlying presheaf of the image of `F` under `elementsTotalFunctor` is the total presheaf
`Σ_Z F`. -/
@[simp] lemma elementsTotalFunctor_obj_left
    (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) :
    ((elementsTotalFunctor Z).obj F).left = elementsTotalPresheaf Z F :=
  rfl

/-! ### The equivalence -/

/-- **The fibre of a total presheaf.** The sections of `Σ_Z F` over `V` lying over a point `z` of
`Z` are the sections of `F` at `(V, z)`: such a section is the pair `(z, s)`, and its first
component is pinned down by the fibre condition. -/
def totalFibreEquiv (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v)
    (a : (presheafOfCategories (Z ⋙ typeToCat)).obj) :
    F.obj (op a) ≃ {p : (elementsTotalPresheaf Z F).obj (op a.base) // p.1 = a.fiber.as} where
  toFun s := ⟨⟨a.fiber.as, s⟩, rfl⟩
  invFun p := cast (congrArg (fun t => F.obj (op (elementsPoint Z t))) p.2) p.1.2
  left_inv s := rfl
  right_inv := by
    rintro ⟨⟨t, s⟩, h⟩
    have h' : t = a.fiber.as := h
    subst h'
    rfl

/-- The unit of the equivalence: a presheaf on the category of elements of `Z` is the presheaf of
fibres of its total presheaf. -/
def elementsTotalUnitIso :
    𝟭 (((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) ≅
      elementsTotalFunctor Z ⋙ elementsFibrePresheaf Z :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun a => Equiv.toIso (totalFibreEquiv Z F a.unop))
      (by
        intro a b h
        ext s
        refine Subtype.ext ?_
        exact totalMk_eq Z F s h.unop
          (elementsRestrict Z ((discreteProjection Z).map h.unop).op a.unop.fiber.as) rfl))
    (by
      intro F G α
      ext a s
      exact Subtype.ext rfl)

/-- The counit of the equivalence: an object over `Z` is the total presheaf of its presheaf of
fibres, because its sections over `V` are partitioned by the point of `Z` they lie over. -/
def elementsTotalCounitIso : elementsFibrePresheaf Z ⋙ elementsTotalFunctor Z ≅ 𝟭 (Over Z) :=
  NatIso.ofComponents
    (fun X => Over.isoMk
      (NatIso.ofComponents (fun V => Equiv.toIso (Equiv.sigmaFiberEquiv fun s => X.hom.app V s))
        (by intro V W f; ext p; rfl))
      (by ext V p; exact p.2.2))
    (by intro X Y g; ext V p; rfl)

/-- **Presheaves on the category of elements of `Z` are presheaves over `Z`.** The total presheaf
and the presheaf of fibres are an equivalence of categories `PSh(El Z) ≌ Over Z`. -/
@[sga "4 I 5.11"]
def elementsTotalEquivalence :
    (((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) ≌ Over Z :=
  .mk (elementsTotalFunctor Z) (elementsFibrePresheaf Z) (elementsTotalUnitIso Z)
    (elementsTotalCounitIso Z)

/-- The total presheaf functor `PSh(El Z) ⥤ Over Z` is an equivalence of categories. -/
instance isEquivalence_elementsTotalFunctor : (elementsTotalFunctor Z).IsEquivalence :=
  (elementsTotalEquivalence Z).isEquivalence_functor

/-- The presheaf of fibres functor `Over Z ⥤ PSh(El Z)` is an equivalence of categories. -/
instance isEquivalence_elementsFibrePresheaf : (elementsFibrePresheaf Z).IsEquivalence :=
  (elementsTotalEquivalence Z).isEquivalence_inverse

/-! ### The equivalence is cartesian monoidal -/

section Monoidal

variable [CartesianMonoidalCategory (Over Z)]

/-- **The total presheaf is a product-preserving functor.** The equivalence `PSh(El Z) ≌ Over Z`
preserves finite products, so it is monoidal for the cartesian monoidal structures: the fibre
product over `Z` of two total presheaves is the total presheaf of the product. -/
@[instance_reducible]
noncomputable def elementsTotalFunctorMonoidal : (elementsTotalFunctor Z).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The presheaf of fibres is a product-preserving functor: it takes the fibre product over `Z`
to the product of presheaves on the category of elements of `Z`. -/
@[instance_reducible]
noncomputable def elementsFibrePresheafMonoidal : (elementsFibrePresheaf Z).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- **Presheaves of groups on the category of elements of `Z` are group objects over `Z`.** The
equivalence `PSh(El Z) ≌ Over Z` preserves finite products, so it lifts to the categories of
group objects; on the left these are the presheaves of groups on the category of elements of `Z`
and on the right the group objects of the slice, whose multiplication is defined on the fibre
product over `Z`. -/
noncomputable def elementsTotalGrpEquivalence :
    Grp (((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v) ≌ Grp (Over Z) :=
  letI : (elementsTotalEquivalence Z).functor.Monoidal := elementsTotalFunctorMonoidal Z
  letI : (elementsTotalEquivalence Z).inverse.Monoidal := elementsFibrePresheafMonoidal Z
  Equivalence.mapGrp (elementsTotalEquivalence Z)

end Monoidal

end CategoryTheory.PresheafOfCategories

end
