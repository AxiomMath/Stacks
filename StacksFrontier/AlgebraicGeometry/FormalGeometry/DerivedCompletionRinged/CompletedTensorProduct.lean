module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedHomComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeReflector
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
import StacksCore.Tactic.StacksAttribute

/-!
# The completed tensor product on a ringed site

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals of finite type and `K ↦ K^∧` the left
adjoint of the inclusion `D_comp(𝒪) ⥤ D(𝒪)` of [Stacks, Tag 099F]. The *completed tensor
product* of [Stacks, Tag 099G] is

`K ⊗^∧_𝒪 L = (K ⊗^𝐋_𝒪 L)^∧`.

It is a functor `D_comp(𝒪) × D_comp(𝒪) ⥤ D_comp(𝒪)`, and for derived-complete `K`, `L`, `M`

`Hom_{D_comp(𝒪)}(K, R𝑆heafHom_𝒪(L, M)) = Hom_{D_comp(𝒪)}(K ⊗^∧_𝒪 L, M)`,

the internal Hom on the left being derived complete by [Stacks, Tag 099A].

## Main definitions

* `AlgebraicGeometry.RingedSite.completeDerivedSheafHom`: the derived internal Hom of two
  derived-complete objects, as a derived-complete object; at an arbitrary sheaf of ideals.
* `AlgebraicGeometry.RingedSite.completedTensorProduct`: the completed tensor product, as a
  bifunctor on the derived-complete objects, and
  `AlgebraicGeometry.RingedSite.completedTensorProductProd`: the same functor on the product
  category, which is the shape [Stacks, Tag 099G] states.
* `AlgebraicGeometry.RingedSite.completedTensorHomEquiv`: the bijection
  `Hom(K, R𝑆heafHom_𝒪(L, M)) ≃ Hom(K ⊗^∧_𝒪 L, M)` on the derived-complete objects.
* `AlgebraicGeometry.RingedSite.completedTensorProductOfIsRightAdjoint` and
  `AlgebraicGeometry.RingedSite.completedTensorHomEquivOfIsRightAdjoint`: the same constructions
  from an arbitrary left adjoint of the inclusion `D_comp(𝒪) ⥤ D(𝒪)`, at an arbitrary sheaf of
  ideals.

## Main results

* `AlgebraicGeometry.RingedSite.ι_completedTensorProduct_obj_obj`: the completed tensor product
  of `K` and `L` is, as an object of `D(𝒪)`, the derived completion of `K ⊗^𝐋_𝒪 L`.
* `AlgebraicGeometry.RingedSite.ι_completeDerivedSheafHom_obj_obj`: the derived internal Hom of
  two derived-complete objects is, as an object of `D(𝒪)`, their derived internal Hom.

## Implementation notes

The construction uses nothing about the derived completion functor beyond its being a left
adjoint of the inclusion `D_comp(𝒪) ⥤ D(𝒪)`, so it is first carried out from an arbitrary such
left adjoint, given as an instance argument (the `OfIsRightAdjoint` declarations). The tag's
declarations then take only the finite-type hypothesis on `ℐ`, and the left adjoint is the one
of [Stacks, Tag 099F], `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of
`FiniteTypeReflector.lean`, found by instance search.

The bijection is the source's chain of three. Both outer Hom-groups are taken in `D_comp(𝒪)`,
the full subcategory of `D(𝒪)` cut out by `AlgebraicGeometry.RingedSite.IsDerivedComplete`, so
each is the corresponding Hom-group of `D(𝒪)` by the full faithfulness of the inclusion. The
middle bijection is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, the
tensor–internal-Hom bijection of [Stacks, Tag 08J8]; the outer one is the reflector adjunction
at the derived-complete `M`. The derived internal Hom lands in `D_comp(𝒪)` by
[Stacks, Tag 099A], `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedSheafHom`, which is
where the derived completeness of `M` — and nothing about `L` — is used; that assertion needs no
hypothesis on `ℐ`, and is stated at an arbitrary sheaf of ideals.

The universes are those at which the inputs meet: a `RingedSite.{u, u, u}` with modules in
`SheafOfModules.{u}`. The derived tensor product of [Stacks, Tag 06YU] exists only there,
because the K-flat resolutions it rests on are available only there, and its instance
hypotheses are discharged there. The derived category is the
standard model, which the predicate `IsDerivedComplete` carries in its type.

## References

* [Stacks Project, Tag 099A](https://stacks.math.columbia.edu/tag/099A)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099G](https://stacks.math.columbia.edu/tag/099G)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The derived internal Hom of derived-complete objects is derived complete**, so it is a
bifunctor `D_comp(𝒪)ᵒᵖ × D_comp(𝒪) ⥤ D_comp(𝒪)`. This is the last assertion of
[Stacks, Tag 099G], and it is [Stacks, Tag 099A] — which asks nothing of the source — applied
to a derived-complete target. -/
@[stacks 099G "the assertion `R𝑆heafHom_𝒪(L, M) ∈ D_comp(𝒪)` for `L, M ∈ D_comp(𝒪)`, which the
  tag records at the end and attributes to [Stacks, Tag 099A], as the induced bifunctor on the
  derived-complete objects; it holds for every sheaf of ideals"]
def completeDerivedSheafHom :
    (ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I))ᵒᵖ ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
        ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) :=
  Functor.curry.obj
    (ObjectProperty.lift (IsDerivedComplete.{u, u, u, u} X I)
      ((ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).op.prod
          (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor X))
      (fun p ↦ isDerivedComplete_derivedSheafHom X I _ _ p.2.property))

/-- The underlying object of `D(𝒪)` of the derived internal Hom of two derived-complete objects
is the derived internal Hom of their underlying objects. -/
theorem ι_completeDerivedSheafHom_obj_obj
    (L M : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (((completeDerivedSheafHom X I).obj (op L)).obj M).obj =
      ((derivedSheafHomBifunctor X).obj (op L.obj)).obj M.obj :=
  rfl

section Reflector

/-! ### The construction from an arbitrary reflector

The completed tensor product and its adjunction use nothing about the derived completion
functor beyond its being *a* left adjoint of the inclusion `D_comp(𝒪) ⥤ D(𝒪)`. This section
builds both from that datum, taken as an instance argument; the next section feeds it the
reflector of [Stacks, Tag 099F]. -/

variable [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- The completed tensor product `K ⊗^∧_𝒪 L = (K ⊗^𝐋_𝒪 L)^∧` of two derived-complete objects,
built from an arbitrary left adjoint `(-)^∧` of the inclusion `D_comp(𝒪) ⥤ D(𝒪)`; the
completion of any object is derived complete, so this is a bifunctor on the derived-complete
objects. `completedTensorProduct` is this at the reflector of [Stacks, Tag 099F]. -/
def completedTensorProductOfIsRightAdjoint :
    ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
        ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) :=
  ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I) ⋙
    Stacks.SheafOfModules.derivedTensorProductFunctor X ⋙
      (Functor.whiskeringLeft _ _ _).obj
          (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint

/-- The completed tensor product of `K` and `L`, built from a left adjoint of the inclusion,
is, as an object of `D(𝒪)`, the derived completion of `K ⊗^𝐋_𝒪 L`. -/
theorem ι_completedTensorProductOfIsRightAdjoint_obj_obj
    (K L : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (((completedTensorProductOfIsRightAdjoint X I).obj K).obj L).obj =
      (derivedCompletion X I).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K.obj).obj L.obj) :=
  rfl

/-- The tensor–internal-Hom adjunction on the derived-complete objects, built from an arbitrary
left adjoint of the inclusion: for derived-complete `K`, `L` and `M`,

`Hom_{D_comp(𝒪)}(K, R𝑆heafHom_𝒪(L, M)) = Hom_{D_comp(𝒪)}(K ⊗^∧_𝒪 L, M)`.

It is, in order, the full faithfulness of `D_comp(𝒪) ⥤ D(𝒪)`, the tensor–internal-Hom
bijection `derivedCurryHomEquiv` of [Stacks, Tag 08J8], and the inverse of the hom-set
bijection of the adjunction `(-)^∧ ⊣ ι` at the derived-complete `M`. So its value at `g` is the
unique morphism out of `(K ⊗^𝐋_𝒪 L)^∧` whose composite with the unit
`K ⊗^𝐋_𝒪 L ⟶ (K ⊗^𝐋_𝒪 L)^∧` is the morphism of [Stacks, Tag 08J8] attached to `g`. -/
def completedTensorHomEquivOfIsRightAdjoint
    (K L M : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (K ⟶ ((completeDerivedSheafHom X I).obj (op L)).obj M) ≃
      (((completedTensorProductOfIsRightAdjoint X I).obj K).obj L ⟶ M) :=
  (ObjectProperty.fullyFaithfulι (IsDerivedComplete.{u, u, u, u} X I)).homEquiv.trans
    ((derivedCurryHomEquiv X K.obj L.obj M.obj).toEquiv.trans
      ((derivedCompletionAdjunction X I).homEquiv
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K.obj).obj L.obj) M).symm)

end Reflector

section FiniteType

/-! ### At a sheaf of ideals of finite type

Here the left adjoint of the inclusion is the derived completion functor of
[Stacks, Tag 099F], found by instance search from the finite-type hypothesis. -/

variable [I.toSheafOfModules.IsFiniteType]

/-- **The completed tensor product of [Stacks, Tag 099G].** For `ℐ` of finite type and
derived-complete `K` and `L`, `K ⊗^∧_𝒪 L = (K ⊗^𝐋_𝒪 L)^∧`, where `(-)^∧` is the derived
completion functor of [Stacks, Tag 099F]; the completion of any object is derived complete, so
this is a bifunctor on the derived-complete objects. -/
@[stacks 099G "the completed tensor product `K ⊗^∧_𝒪 L = (K ⊗^𝐋_𝒪 L)^∧` and its functoriality
  in each variable, as a bifunctor on `D_comp(𝒪)`"]
def completedTensorProduct :
    ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
        ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) :=
  completedTensorProductOfIsRightAdjoint X I

/-- **The completed tensor product as a functor `D_comp(𝒪) × D_comp(𝒪) ⥤ D_comp(𝒪)`**, the
shape in which [Stacks, Tag 099G] states it, for `ℐ` of finite type. -/
@[stacks 099G "the completed tensor product as a functor `D_comp(𝒪) × D_comp(𝒪) → D_comp(𝒪)`"]
def completedTensorProductProd :
    ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ×
        ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) :=
  Functor.uncurry.obj (completedTensorProduct X I)

/-- The completed tensor product of `K` and `L` is, as an object of `D(𝒪)`, the derived
completion of the derived tensor product `K ⊗^𝐋_𝒪 L`. -/
theorem ι_completedTensorProduct_obj_obj
    (K L : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (((completedTensorProduct X I).obj K).obj L).obj =
      (derivedCompletion X I).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K.obj).obj L.obj) :=
  rfl

/-- The completed tensor product on the product category agrees with the bifunctor. -/
theorem completedTensorProductProd_obj
    (K L : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (completedTensorProductProd X I).obj (K, L) =
      ((completedTensorProduct X I).obj K).obj L :=
  rfl

/-- **The adjunction of [Stacks, Tag 099G].** For `ℐ` of finite type and derived-complete `K`,
`L` and `M`,

`Hom_{D_comp(𝒪)}(K, R𝑆heafHom_𝒪(L, M)) = Hom_{D_comp(𝒪)}(K ⊗^∧_𝒪 L, M)`.

It is `completedTensorHomEquivOfIsRightAdjoint` at the derived completion functor of
[Stacks, Tag 099F]: in order, the full faithfulness of `D_comp(𝒪) ⥤ D(𝒪)`, the bijection of
[Stacks, Tag 08J8], and the inverse of the hom-set bijection of the adjunction of
[Stacks, Tag 099F] at the derived-complete `M`. -/
@[stacks 099G "the bijection
  `Hom_{D_comp(𝒪)}(K, R𝑆heafHom_𝒪(L, M)) = Hom_{D_comp(𝒪)}(K ⊗^∧_𝒪 L, M)` for
  `K, L, M ∈ D_comp(𝒪)`"]
def completedTensorHomEquiv
    (K L M : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)) :
    (K ⟶ ((completeDerivedSheafHom X I).obj (op L)).obj M) ≃
      (((completedTensorProduct X I).obj K).obj L ⟶ M) :=
  completedTensorHomEquivOfIsRightAdjoint X I K L M

end FiniteType


end AlgebraicGeometry.RingedSite

end
