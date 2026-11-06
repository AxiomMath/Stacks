module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismGroupOverSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaGroupAxioms
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements

/-!
# The group law on the relative sheaf of automorphisms

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S` and let `x : Z ⟶ 𝒳` be an algebraic-space-valued point of `𝒳`. The 2-fibre product

```text
Isom_{𝒳/𝒴}(x, x) = Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}
```

(`AlgebraicGeometry.Stack.relativeAutomorphismSpaceOverSpace`) is equivalent, as a category over
`Z`, to the category of elements of the presheaf of groups
`AlgebraicGeometry.Stack.relativeAutomorphismGroupPresheaf`, whose sections at a point `a` of `Z`
are the vertical automorphisms of `x(a)` killed by `f`, with composition as the group law. Under
this equivalence the multiplication, the unit and the inverse are the composition law, the
neutral section and the inverse of the relative inertia, pulled back along `x`.

## Main definitions

* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.objAutomorphism`: the relative automorphism
  of `x` carried by an object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`, namely the conjugate of its inertia
  component by its comparison isomorphism.
* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.inertiaObj`: conversely, the object
  `(x(a), φ)` of the relative inertia attached to a relative automorphism `φ` at `a`.
* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.comparison`: the comparison 1-morphism from
  the category of elements of the presheaf of relative automorphisms to `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`.
* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.inertiaPair`: the object of
  `ℐ_{𝒳/𝒴} ×_𝒳 ℐ_{𝒳/𝒴}` made of two relative automorphisms at one point.

## Main results

* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.nonempty_isEquivalenceOver_comparison` and
  `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.nonempty_equivalenceOver_comparison`:
  `Isom_{𝒳/𝒴}(x, x)` is equivalent over `Z` to the category of elements of the presheaf of
  relative automorphisms of `x`.
* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.inertiaObj_mul`, `…inertiaObj_one` and
  `…inertiaObj_inv`: the multiplication, the unit and the inverse of relative automorphisms are
  `CategoryTheory.RelativeInertia.composition`, `…neutralSection` and `…inverse`.
* `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.comparison_comp_proj`: the comparison is
  strictly over `Z`.

## Implementation notes

The equivalence is produced by
`CategoryTheory.nonempty_isEquivalenceOver_of_forall_verticalObjPreimage`: a fully faithful
1-morphism over a base all of whose objectwise preimages are reached by a *vertical* isomorphism
is an equivalence over that base. Full faithfulness is where the two sides meet: a morphism of
the category of elements is determined by the morphism of `Z` it lies over, and the datum it
carries — that the automorphism upstairs restricts to the one downstairs — is exactly the
commuting square of a morphism of the relative inertia, by the characterisation
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict_fac` of restriction and its
uniqueness.

Two sources of friction, both handled the same way. The comparison isomorphism `A.iso` of an
object of the 2-fibre product has type `x(A.x) ≅ π(A.y)` while the automorphism `A.y.auto` lives
on `A.y.obj`; the two agree only up to unfolding `CategoryTheory.RelativeInertia.π`, so every
statement about the conjugate is phrased through
`AlgebraicGeometry.Stack.RelativeAutomorphismSpace.objIso`, whose type ascription forces the
second form. And a goal mentioning the `eqToHom` of the base equality of an object of the
2-fibre product is not type-correct at the `implicit` transparency level that `rw`/`simp` use for
their matching, so those goals are discharged either by destructuring the object and
substituting its base equality away, or by a proof term.

## References

* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack.RelativeAutomorphismSpace

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.RelativeInertia.basedCategory CategoryTheory.RelativeInertia.basedProjection
  CategoryTheory.RelativeInertia.π CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.TwoFibreProductOver.fst

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
variable (f : 𝒳 ⟶ 𝒴) (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-- The comparison isomorphism of an object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`, read as an isomorphism
onto the underlying object of the inertia. -/
abbrev objIso (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    x.hom.hom.toFunctor.obj A.x ≅ A.y.obj := A.iso

/-- The conjugate of the automorphism of an object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` is vertical. -/
lemma isHomLift_objConjugate (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    𝒳.val.val.p.IsHomLift (𝟙 A.base)
      ((objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv) := by
  have h1 : 𝒳.val.val.p.IsHomLift (𝟙 A.base) (objIso B S hS Z hZ f x A).hom := A.vertical
  have hy : 𝒳.val.val.p.obj A.y.obj = A.base := A.hy
  have h2 : 𝒳.val.val.p.IsHomLift (𝟙 A.base) A.y.auto.asIso.hom :=
    (congrArg (fun U => 𝒳.val.val.p.IsHomLift (𝟙 U) A.y.auto.asIso.hom) hy).mp
      (isHomLift_of_map_eq_id B S hS f A.y.auto.asIso.hom A.y.cond)
  have h3 : 𝒳.val.val.p.IsHomLift (𝟙 A.base) (objIso B S hS Z hZ f x A).inv := by
    rw [← IsIso.Iso.inv_hom]
    exact IsHomLift.lift_id_inv_isIso 𝒳.val.val.p A.base (objIso B S hS Z hZ f x A).hom
  have hc : 𝒳.val.val.p.IsHomLift (𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base)
      ((objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv) :=
    inferInstance
  simpa using hc

/-- **The relative automorphism of `x` carried by an object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`:** the
automorphism of the object of the inertia, conjugated into an automorphism of `x` at the
underlying point of `Z` by the comparison isomorphism. -/
def objAutomorphism (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    RelativeAutomorphism B S hS Z hZ f x A.x := by
  refine ⟨⟨(objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv, ?_⟩, ?_⟩
  · exact (congrArg (fun U => 𝒳.val.val.p.IsHomLift (𝟙 U)
      ((objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv))
        A.hx).mpr (isHomLift_objConjugate B S hS Z hZ f x A)
  · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, A.y.cond,
      Category.id_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]

/-- The automorphism underlying `objAutomorphism A` is the conjugate of the automorphism of the
object of the inertia by the comparison isomorphism. -/
@[simp] lemma objAutomorphism_val
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (objAutomorphism B S hS Z hZ f x A).1.1 =
      (objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv := rfl

/-- The object `(x(a), φ)` of the relative inertia attached to a relative automorphism `φ` of
`x` at a point `a` of `Z`. -/
noncomputable def inertiaObj
    {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    CategoryTheory.RelativeInertia f.hom.hom.toFunctor where
  obj := x.hom.hom.toFunctor.obj a
  auto :=
    haveI := VertHom.isIso_val 𝒳.val.isFiberedInGroupoids φ.1
    Aut.of (asIso φ.1.1)
  cond := φ.2

/-- The underlying object of `inertiaObj φ` is `x(a)`. -/
@[simp] lemma inertiaObj_obj
    {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    (inertiaObj B S hS Z hZ f x φ).obj = x.hom.hom.toFunctor.obj a := rfl

/-- The automorphism of `inertiaObj φ` is `φ`. -/
@[simp] lemma inertiaObj_auto_hom
    {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    (inertiaObj B S hS Z hZ f x φ).auto.asIso.hom = φ.1.1 := rfl

/-- **The comparison 1-morphism** from the category of elements of the presheaf of relative
automorphisms to `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`: a relative automorphism `φ` of `x` at a point `a` of `Z`
is sent to the triple `(a, (x(a), φ), 𝟙)`. -/
noncomputable def comparison :
    (presheafOfCategories (relativeAutomorphismPresheaf B S hS Z hZ f x ⋙ typeToCat)).obj ⥤
      (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj where
  obj M :=
    { base := (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj M.base
      x := M.base
      y := inertiaObj B S hS Z hZ f x M.fiber.as
      hx := rfl
      hy := Functor.congr_obj x.hom.hom.w M.base
      iso := Iso.refl _
      vertical := RelativeAutomorphism.isHomLift_id B S hS Z hZ x M.base }
  map {M N} u :=
    { hbase := (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.map u.base
      a := u.base
      b :=
        { hom := x.hom.hom.toFunctor.map u.base
          comm := by
            have he : M.fiber.as =
                RelativeAutomorphism.restrict B S hS Z hZ f x u.base N.fiber.as :=
              Discrete.eq_of_hom u.fiber
            change x.hom.hom.toFunctor.map u.base ≫ N.fiber.as.1.1 =
              M.fiber.as.1.1 ≫ x.hom.hom.toFunctor.map u.base
            rw [he]
            exact (VertHom.restrict_fac 𝒳.val.isFiberedInGroupoids
              (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor)
              x.hom.hom.w x.hom.hom.w u.base N.fiber.as.1).symm }
      ha := IsHomLift.map _ u.base
      hb := (CategoryTheory.RelativeInertia.isHomLift_π_comp_iff (p := 𝒳.val.val.p) _ _).mpr
        (VertHom.isHomLift_map (Y₂ := x.hom.hom.toFunctor) x.hom.hom.w u.base)
      w := (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id M := CategoryTheory.TwoFibreProductOver.Hom.ext' rfl
    (CategoryTheory.RelativeInertiaHom.ext
      (show x.hom.hom.toFunctor.map (𝟙 M.base) = 𝟙 _ from
        CategoryTheory.Functor.map_id _ _))
  map_comp u v := CategoryTheory.TwoFibreProductOver.Hom.ext' rfl
    (CategoryTheory.RelativeInertiaHom.ext
      (show x.hom.hom.toFunctor.map (u.base ≫ v.base) =
          x.hom.hom.toFunctor.map u.base ≫ x.hom.hom.toFunctor.map v.base from
        CategoryTheory.Functor.map_comp _ _ _))

/-- The point of `Z` underlying the image of `M` under `comparison` is the base of `M`. -/
@[simp] lemma comparison_obj_x
    (M : (presheafOfCategories (relativeAutomorphismPresheaf B S hS Z hZ f x ⋙ typeToCat)).obj) :
    ((comparison B S hS Z hZ f x).obj M).x = M.base := rfl

/-- The morphism of `Z` underlying the image of `u` under `comparison` is the base of `u`. -/
@[simp] lemma comparison_map_a
    {M N : (presheafOfCategories
      (relativeAutomorphismPresheaf B S hS Z hZ f x ⋙ typeToCat)).obj} (u : M ⟶ N) :
    ((comparison B S hS Z hZ f x).map u).a = u.base := rfl

/-- The morphism of the inertia underlying the image of `u` under `comparison` is `x` applied to
the base of `u`. -/
@[simp] lemma comparison_map_b_hom
    {M N : (presheafOfCategories
      (relativeAutomorphismPresheaf B S hS Z hZ f x ⋙ typeToCat)).obj} (u : M ⟶ N) :
    ((comparison B S hS Z hZ f x).map u).b.hom =
      x.hom.hom.toFunctor.map u.base := rfl

/-- **The comparison 1-morphism is strictly over `Z`**: followed by the projection
`Isom_{𝒳/𝒴}(x, x) ⟶ Z` it is the projection of the category of elements of the presheaf of
relative automorphisms. -/
lemma comparison_comp_proj :
    comparison B S hS Z hZ f x ⋙
        (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x).toFunctor =
      PresheafOfCategories.discreteProjection
        (relativeAutomorphismPresheaf B S hS Z hZ f x) :=
  rfl

/-- The comparison 1-morphism is faithful. -/
instance : (comparison B S hS Z hZ f x).Faithful where
  map_injective {M N} {u v} h := by
    obtain ⟨ub, uf⟩ := u
    obtain ⟨vb, vf⟩ := v
    have hb : ub = vb := congrArg (fun ρ => ρ.a) h
    subst hb
    congr 1
    exact Discrete.hom_eq

/-- The comparison 1-morphism is full. -/
instance : (comparison B S hS Z hZ f x).Full where
  map_surjective {M N} ρ := by
    have hw : x.hom.hom.toFunctor.map ρ.a ≫ 𝟙 (x.hom.hom.toFunctor.obj N.base) =
        𝟙 (x.hom.hom.toFunctor.obj M.base) ≫ ρ.b.hom := ρ.w
    have hbhom : ρ.b.hom = x.hom.hom.toFunctor.map ρ.a :=
      (Category.id_comp _).symm.trans (hw.symm.trans (Category.comp_id _))
    have hcomm : x.hom.hom.toFunctor.map ρ.a ≫ N.fiber.as.1.1 =
        M.fiber.as.1.1 ≫ x.hom.hom.toFunctor.map ρ.a :=
      hbhom ▸ ρ.b.comm
    have hres : M.fiber.as =
        RelativeAutomorphism.restrict B S hS Z hZ f x ρ.a N.fiber.as :=
      Subtype.ext (VertHom.restrict_uniq 𝒳.val.isFiberedInGroupoids
        (Y₁ := x.hom.hom.toFunctor) (Y₂ := x.hom.hom.toFunctor)
        x.hom.hom.w x.hom.hom.w ρ.a N.fiber.as.1 M.fiber.as.1 hcomm.symm)
    refine ⟨⟨ρ.a, Discrete.eqToHom hres⟩, ?_⟩
    exact CategoryTheory.TwoFibreProductOver.Hom.ext' rfl
      (CategoryTheory.RelativeInertiaHom.ext hbhom.symm)

/-- The object of the category of elements of the presheaf of relative automorphisms named by an
object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`: its point of `Z` together with the relative automorphism of `x`
it carries there. -/
def objElement (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (presheafOfCategories (relativeAutomorphismPresheaf B S hS Z hZ f x ⋙ typeToCat)).obj :=
  ⟨A.x, Discrete.mk (objAutomorphism B S hS Z hZ f x A)⟩

/-- The identity of the point of `Z` underlying an object `A` of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` lies over
`eqToHom A.hx.symm`. -/
lemma isHomLift_eqToHom_hx_symm
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (eqToHom A.hx.symm) (𝟙 A.x) := by
  exact IsHomLift.id_lift_eqToHom_codomain A.hx.symm rfl

/-- The identity of the point of `Z` underlying an object `A` of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` lies over
`eqToHom A.hx`. -/
lemma isHomLift_eqToHom_hx
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (eqToHom A.hx) (𝟙 A.x) := by
  exact IsHomLift.id_lift_eqToHom_domain A.hx rfl

/-- The comparison isomorphism of an object `A` of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` lies over
`eqToHom A.hx`. -/
lemma isHomLift_eqToHom_objIso_hom
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    𝒳.val.val.p.IsHomLift (eqToHom A.hx) (objIso B S hS Z hZ f x A).hom := by
  obtain ⟨base, a, Y, hx, hy, iso, vert⟩ := A
  subst hx
  exact vert

/-- The inverse of the comparison isomorphism of an object `A` of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` lies over
`eqToHom A.hx.symm`. -/
lemma isHomLift_eqToHom_objIso_inv
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    𝒳.val.val.p.IsHomLift (eqToHom A.hx.symm) (objIso B S hS Z hZ f x A).inv := by
  obtain ⟨base, a, Y, hx, hy, iso, vert⟩ := A
  subst hx
  have := vert
  exact IsHomLift.lift_id_inv 𝒳.val.val.p _ iso

/-- The morphism from an object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` to the standard object `(a, (x(a), φ), 𝟙)`
carrying the same relative automorphism, with identity `Z`-component and the inverse comparison
isomorphism as inertia component. -/
noncomputable def objElementIsoHom
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    A ⟶ (comparison B S hS Z hZ f x).obj
      (objElement B S hS Z hZ f x A) where
  hbase := eqToHom A.hx.symm
  a := 𝟙 A.x
  b :=
    { hom := (objIso B S hS Z hZ f x A).inv
      comm := by
        change (objIso B S hS Z hZ f x A).inv ≫ (objIso B S hS Z hZ f x A).hom ≫
            A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv =
          A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv
        simp }
  ha := isHomLift_eqToHom_hx_symm B S hS Z hZ f x A
  hb := (CategoryTheory.RelativeInertia.isHomLift_π_comp_iff (p := 𝒳.val.val.p) _ _).mpr
    (isHomLift_eqToHom_objIso_inv B S hS Z hZ f x A)
  w :=
    (Category.comp_id _).trans ((CategoryTheory.Functor.map_id _ _).trans
      (Iso.hom_inv_id (objIso B S hS Z hZ f x A)).symm)

/-- The inverse of `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.objElementIsoHom`. -/
noncomputable def objElementIsoInv
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (comparison B S hS Z hZ f x).obj
      (objElement B S hS Z hZ f x A) ⟶ A where
  hbase := eqToHom A.hx
  a := 𝟙 A.x
  b :=
    { hom := (objIso B S hS Z hZ f x A).hom
      comm := by
        change (objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom =
          ((objIso B S hS Z hZ f x A).hom ≫ A.y.auto.asIso.hom ≫ (objIso B S hS Z hZ f x A).inv) ≫
            (objIso B S hS Z hZ f x A).hom
        simp }
  ha := isHomLift_eqToHom_hx B S hS Z hZ f x A
  hb := (CategoryTheory.RelativeInertia.isHomLift_π_comp_iff (p := 𝒳.val.val.p) _ _).mpr
    (isHomLift_eqToHom_objIso_hom B S hS Z hZ f x A)
  w := congrArg (fun t => t ≫ (objIso B S hS Z hZ f x A).hom)
    (CategoryTheory.Functor.map_id x.hom.hom.toFunctor A.x)

/-- **Every object of `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}` is isomorphic, over `Z`, to the standard object
carrying the same relative automorphism**, by
`AlgebraicGeometry.Stack.RelativeAutomorphismSpace.objElementIsoHom`. -/
noncomputable def objElementIso
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    A ≅ (comparison B S hS Z hZ f x).obj
      (objElement B S hS Z hZ f x A) where
  hom := objElementIsoHom B S hS Z hZ f x A
  inv := objElementIsoInv B S hS Z hZ f x A
  hom_inv_id := CategoryTheory.TwoFibreProductOver.Hom.ext'
    (show 𝟙 A.x ≫ 𝟙 A.x = 𝟙 A.x from Category.comp_id _)
    (CategoryTheory.RelativeInertiaHom.ext
      (show (objIso B S hS Z hZ f x A).inv ≫ (objIso B S hS Z hZ f x A).hom = 𝟙 A.y.obj from
        Iso.inv_hom_id _))
  inv_hom_id := CategoryTheory.TwoFibreProductOver.Hom.ext'
    (show 𝟙 A.x ≫ 𝟙 A.x = 𝟙 A.x from Category.comp_id _)
    (CategoryTheory.RelativeInertiaHom.ext
      (show (objIso B S hS Z hZ f x A).hom ≫ (objIso B S hS Z hZ f x A).inv =
          𝟙 (x.hom.hom.toFunctor.obj A.x) from Iso.hom_inv_id _))

/-- The projection to `Z` of `AlgebraicGeometry.Stack.RelativeAutomorphismSpace.objElementIso A`
is the identity of the point of `Z` underlying `A`. -/
lemma proj_map_objElementIso_hom
    (A : (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.obj) :
    (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x).toFunctor.map
      (objElementIso B S hS Z hZ f x A).hom = 𝟙 A.x := rfl

/-- **The group structure on `Isom_{𝒳/𝒴}(x, x)` over `Z`.** The comparison 1-morphism is an
equivalence over `Z` from the category of elements of the presheaf of groups of relative
automorphisms of `x` (`AlgebraicGeometry.Stack.relativeAutomorphismGroupPresheaf`) to
`Isom_{𝒳/𝒴}(x, x) = Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`. -/
@[stacks 06PP "part (1): the group structure on Isom_{X/Y}(x, x) over Z"]
theorem nonempty_isEquivalenceOver_comparison :
    Nonempty (CategoryTheory.IsEquivalenceOver
      (PresheafOfCategories.discreteProjection (relativeAutomorphismPresheaf B S hS Z hZ f x))
      (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x).toFunctor
      (comparison B S hS Z hZ f x)) :=
  CategoryTheory.nonempty_isEquivalenceOver_of_forall_verticalObjPreimage _ _ _
    (comparison_comp_proj B S hS Z hZ f x)
    (fun A => ⟨objElement B S hS Z hZ f x A, rfl, objElementIso B S hS Z hZ f x A,
      (proj_map_objElementIso_hom B S hS Z hZ f x A).trans (eqToHom_refl _ _).symm⟩)

/-- **`Isom_{𝒳/𝒴}(x, x)` is the presheaf of relative automorphisms, as a category over `Z`**:
there is a `StacksRepresentableCFG.EquivalenceOver` from the projection of the category of
elements of the presheaf of relative automorphisms of `x` to the projection
`Isom_{𝒳/𝒴}(x, x) ⟶ Z`. -/
@[stacks 06PP "part (1): Isom_{X/Y}(x, x) is the presheaf of groups of relative automorphisms"]
theorem nonempty_equivalenceOver_comparison :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (PresheafOfCategories.discreteProjection (relativeAutomorphismPresheaf B S hS Z hZ f x))
      (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x).toFunctor) :=
  (nonempty_isEquivalenceOver_comparison B S hS Z hZ f x).map
    StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver

/-! ### The group law is the composition law of the relative inertia -/

/-- The object of the 2-fibre product `ℐ_{𝒳/𝒴} ×_𝒳 ℐ_{𝒳/𝒴}` made of two relative automorphisms
of `x` at one point `a` of `Z`: both have underlying object `x(a)`, so the comparison
isomorphism between them is the identity. -/
noncomputable def inertiaPair
    {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ ψ : RelativeAutomorphism B S hS Z hZ f x a) :
    CategoryTheory.TwoFibreProductOver
      (CategoryTheory.RelativeInertia.π f.hom.hom.toFunctor ⋙ 𝒳.val.val.p)
      (CategoryTheory.RelativeInertia.π f.hom.hom.toFunctor ⋙ 𝒳.val.val.p)
      𝒳.val.val.p (CategoryTheory.RelativeInertia.π f.hom.hom.toFunctor)
      (CategoryTheory.RelativeInertia.π f.hom.hom.toFunctor) where
  base := 𝒳.val.val.p.obj (x.hom.hom.toFunctor.obj a)
  x := inertiaObj B S hS Z hZ f x φ
  y := inertiaObj B S hS Z hZ f x ψ
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- **The multiplication of relative automorphisms is the composition law of the relative
inertia.** The object of the relative inertia attached to the product `φ * ψ` of two
relative automorphisms of `x` at a point of `Z` is the value at the corresponding object of
`ℐ_{𝒳/𝒴} ×_𝒳 ℐ_{𝒳/𝒴}` of `CategoryTheory.RelativeInertia.composition`, the composition law
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`. -/
@[stacks 06PP "part (1): the group law is the composition law of 050R pulled back along x"]
theorem inertiaObj_mul {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ ψ : RelativeAutomorphism B S hS Z hZ f x a) :
    inertiaObj B S hS Z hZ f x (φ * ψ) =
      (CategoryTheory.RelativeInertia.composition f.hom.hom.toFunctor 𝒳.val.val.p).obj
        (inertiaPair B S hS Z hZ f x φ ψ) :=
  CategoryTheory.RelativeInertia.obj_ext rfl (by
    change (φ * ψ).1.1 = 𝟙 _ ≫ (𝟙 _ ≫ ψ.1.1 ≫ 𝟙 _ ≫ φ.1.1) ≫ 𝟙 _
    rw [RelativeAutomorphism.mul_val]
    simp)

/-- **The unit of the group of relative automorphisms is the neutral section of the relative
inertia.** The object of the relative inertia attached to the identity relative automorphism of
`x` at a point `a` of `Z` is the value of `CategoryTheory.RelativeInertia.neutralSection`,
`x ↦ (x, id_x)`, at `x(a)`. -/
@[stacks 06PP "part (1): the unit is the neutral element of 050R pulled back along x"]
theorem inertiaObj_one {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj} :
    inertiaObj B S hS Z hZ f x (1 : RelativeAutomorphism B S hS Z hZ f x a) =
      (CategoryTheory.RelativeInertia.neutralSection f.hom.hom.toFunctor).obj
        (x.hom.hom.toFunctor.obj a) :=
  CategoryTheory.RelativeInertia.obj_ext rfl (by
    change (1 : RelativeAutomorphism B S hS Z hZ f x a).1.1 = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [RelativeAutomorphism.one_val]
    simp)

/-- **The inverse of the group of relative automorphisms is the inverse of the relative
inertia.** The object of the relative inertia attached to `φ⁻¹` is the value at the object
attached to `φ` of `CategoryTheory.RelativeInertia.inverse`, `(x, α) ↦ (x, α⁻¹)`. -/
@[stacks 06PP "part (1): the inverse is the inverse of 050R pulled back along x"]
theorem inertiaObj_inv {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ : RelativeAutomorphism B S hS Z hZ f x a) :
    inertiaObj B S hS Z hZ f x φ⁻¹ =
      (CategoryTheory.RelativeInertia.inverse f.hom.hom.toFunctor).obj
        (inertiaObj B S hS Z hZ f x φ) :=
  CategoryTheory.RelativeInertia.obj_ext rfl
    (haveI := VertHom.isIso_val 𝒳.val.isFiberedInGroupoids φ.1
      show CategoryTheory.inv φ.1.1 = 𝟙 _ ≫ CategoryTheory.inv φ.1.1 ≫ 𝟙 _ from
        ((Category.id_comp _).trans (Category.comp_id _)).symm)

end AlgebraicGeometry.Stack.RelativeAutomorphismSpace

end
