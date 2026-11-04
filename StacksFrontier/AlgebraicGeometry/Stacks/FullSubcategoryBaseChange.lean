module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor

/-!
# The base change of a full-subcategory inclusion along a scheme-valued point

Let `𝒳` be an algebraic stack over `S` and let `P` be a property of its objects inherited along
morphisms: `P b` and `a ⟶ b` give `P a`. Such a property cuts out a full subcategory which is
again fibred in groupoids, and the base change of its inclusion along a scheme-valued point with
values in `V` is identified here with the category of elements of a subfunctor of `yoneda V` on
the big fppf site of `V`, the subfunctor whose sections over `T` are present exactly when `P`
holds at the object of `𝒳` that the point assigns to `T`.

The base change is the 2-fibre product of the Stacks 02ZW predicate, read through its first
projection. It has at most one morphism between two objects over a fixed object of the site,
because the inclusion of a full subcategory is faithful and the comparison isomorphism of an
object of the 2-fibre product determines the second component of a morphism from the first; and
any two objects over the same object are isomorphic, because the inclusion is full. So the
projection is fibred in setoids with subsingleton sets of isomorphism classes, and Stacks 02ZX
in the form `AlgebraicGeometry.exists_equivalenceOver_elements_of_setoids` turns the
identification of those isomorphism classes into an equivalence over the site.

## Main definitions

* `AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor`: the subfunctor of `yoneda V`
  representing the base change.
* `AlgebraicGeometry.Stack.pointsWithin`: the property of an object of an algebraic stack that
  every point of `|𝒳|` seen by it lies in a prescribed set of points.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_fullSubcategoryBased`: the full subcategory cut
  out by a property inherited along morphisms is fibred in groupoids.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`: the
  identification of the base change with the category of elements of that subfunctor.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange_pointsWithin`: the
  identification for the points-level property `AlgebraicGeometry.Stack.pointsWithin`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion`: the
  inclusion is representable by algebraic spaces as soon as every such subfunctor is an
  algebraic space, which is the only remaining input.
* `CategoryTheory.TwoFibreProductOver.hom_ext_of_faithful` and
  `CategoryTheory.TwoFibreProductOver.fiber_isThin_fst_of_faithful`: a morphism of a 2-fibre
  product along a faithful 1-morphism is determined by its first component, so the fibres of the
  first projection are thin.

## Implementation notes

The property `P` is carried as a bare implication `(a ⟶ b) → P b → P a` rather than as a
typeclass, because that is the form its points-level instance has and because it already implies
closure under isomorphism, which is the only other closure property used. Condition (1) of
Stacks 04TU for such a `P` is immediate: the domain of a strongly cartesian lift has `P` on the
nose, so `CategoryTheory.Functor.isoOverId_of_prop` supplies the fibrewise reading.

The subfunctor is a subfunctor of `yoneda` of the *terminal* object `𝟙 : V ⟶ V` of the big fppf
site of `V`, which is the reading of `yoneda V` inside that site; its sections over any object
form a subsingleton, since a hom-set into a terminal object does.

Algebraicity of that subfunctor is **not** proved here, and so neither is representability of
the inclusion by algebraic spaces. For the general statement that is unavailable see the module
docstring of `StacksFrontier/AlgebraicGeometry/Stacks/FullyFaithfulMonomorphism.lean`.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism of a 2-fibre product whose second leg is faithful is determined by its first
component: the comparison square expresses the image of the second component in terms of the
first. -/
lemma hom_ext_of_faithful [G.Faithful] {A C : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G}
    {f g : A ⟶ C} (h : Hom.a f = Hom.a g) : f = g := by
  refine Hom.ext' h (G.map_injective ?_)
  have key : A.iso.hom ≫ G.map (Hom.b f) = A.iso.hom ≫ G.map (Hom.b g) := by
    rw [← Hom.w f, ← Hom.w g, h]
  exact (cancel_epi A.iso.hom).mp key

/-- Every fibre of the first projection of a 2-fibre product whose second leg is faithful is
thin: the first component of a morphism of a fibre is determined by the objects it joins. -/
lemma fiber_isThin_fst_of_faithful [G.Faithful] (T : 𝒳) :
    Quiver.IsThin ((fst p𝒳 p𝒴 p𝒮 F G).Fiber T) := by
  refine fun A C => ⟨fun f g => ?_⟩
  apply Functor.Fiber.hom_ext
  refine hom_ext_of_faithful ?_
  have := f.2
  have := g.2
  exact (IsHomLift.fac' (fst p𝒳 p𝒴 p𝒮 F G) (𝟙 T) (Functor.Fiber.fiberInclusion.map f)).trans
    (IsHomLift.fac' (fst p𝒳 p𝒴 p𝒮 F G) (𝟙 T) (Functor.Fiber.fiberInclusion.map g)).symm

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The full subcategory of an algebraic stack cut out by a property of objects inherited along
morphisms is fibred in groupoids over the big fppf site of `S`.

Condition (1) of Stacks 04TU holds on the nose, so the restriction is fibred; its fibres are
groupoids because they embed fully faithfully into the fibres of `𝒳`, which are groupoids. -/
theorem isFiberedInGroupoids_fullSubcategoryBased (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    (fullSubcategoryBased 𝒳 P).p.IsFiberedInGroupoids := by
  set p := 𝒳.val.val.p
  have : p.IsFibered := 𝒳.val.property.isFibered
  have hFib : (P.ι ⋙ p).IsFibered := Functor.isFibered_restrict_of_closed p P
    fun _ φ _ hx => Functor.isoOverId_of_prop (hP φ hx)
  have hGroups : ∀ U : BigFppfOver B S hS, IsGroupoid ((P.ι ⋙ p).Fiber U) := by
    intro U
    have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
    set L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl U
    have : P.ι.Full := ObjectProperty.full_ι P
    have : P.ι.Faithful := ObjectProperty.faithful_ι P
    have : L.Full := Functor.Fiber.full_mapOfComp hrfl U
    have : L.Faithful := Functor.Fiber.faithful_mapOfComp hrfl U
    refine ⟨fun f => ?_⟩
    have : IsIso (L.map f) := (𝒳.val.property.fiber_isGroupoid U).all_isIso (L.map f)
    exact isIso_of_fully_faithful L f
  exact Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr ⟨hFib, hGroups⟩

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {P : ObjectProperty 𝒳.val.val.obj}

/-- The subfunctor of `yoneda V` on the big fppf site of `V` whose sections over `T` are the
morphisms to the terminal object when `P` holds at the object `y T` of `𝒳`, and are empty when
it does not.

Here `y` is a scheme-valued point of `𝒳` with values in `V`, and `yoneda V` is read inside the
site of `V` as `yoneda` of its terminal object. This is a subfunctor because `P` is inherited
along the morphism `y T' ⟶ y T` that a morphism `T' ⟶ T` induces. -/
def fullSubcategoryBaseChangeSubfunctor
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    {V : BigFppfOver B S hS} (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj) :
    Subfunctor (yoneda.obj (Over.mk (𝟙 V.left)) :
      (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u) where
  obj T := fun _ => P (y.obj T.unop)
  map i := fun _ hs => hP (y.map i.unop) hs

variable (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
  {V : BigFppfOver B S hS} (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)

include hP in
/-- The sections of `AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` over an object
of the site form a subsingleton: they are morphisms to a terminal object. -/
theorem subsingleton_fullSubcategoryBaseChangeSubfunctor
    (T : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ) :
    Subsingleton ((fullSubcategoryBaseChangeSubfunctor 𝒳 hP y).toFunctor.obj T) :=
  ⟨fun _ _ => Subtype.ext (Over.mkIdTerminal.hom_ext _ _)⟩

include hP in
/-- An object of the base change lying over `T` witnesses `P` at the object `y T`: its
comparison isomorphism is a morphism from `y T` to an object with `P`. -/
theorem prop_of_fullSubcategoryBaseChange_fibre
    (T : BigFppfOver B V.left.1 V.left.2)
    (A : (TwoFibreProductOver.fst (Over.map V.hom) (fullSubcategoryBased 𝒳 P).p
      𝒳.val.val.p y (fullSubcategoryBasedInclusion 𝒳 P).toFunctor).Fiber T) :
    P (y.obj T) := by
  obtain ⟨A, rfl⟩ := A
  exact hP A.iso.hom A.y.property

/-- The object of the base change lying over `T` attached to a proof that `P` holds at `y T`:
the object `y T` of `𝒳` tagged with that proof, with identity comparison isomorphism. -/
def fullSubcategoryBaseChangeFibre (hy : y ⋙ 𝒳.val.val.p = Over.map V.hom)
    (T : BigFppfOver B V.left.1 V.left.2) (h : P (y.obj T)) :
    (TwoFibreProductOver.fst (Over.map V.hom) (fullSubcategoryBased 𝒳 P).p
      𝒳.val.val.p y (fullSubcategoryBasedInclusion 𝒳 P).toFunctor).Fiber T :=
  ⟨{ base := (Over.map V.hom).obj T
     x := T
     y := ⟨y.obj T, h⟩
     hx := rfl
     hy := Functor.congr_obj hy T
     iso := Iso.refl _
     vertical := IsHomLift.id (Functor.congr_obj hy T) }, rfl⟩

include hP in
/-- **The base change of a full-subcategory inclusion along a scheme-valued point is the
category of elements of a subfunctor of `yoneda V`.**

For a property `P` of the objects of an algebraic stack inherited along morphisms, the first
projection of the 2-fibre product of a scheme-valued point `y` with values in `V` and the
inclusion of the full subcategory cut out by `P` is equivalent, over the big fppf site of `V`,
to the category of elements of
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor`.

Both sides are fibred in setoids with a subsingleton set of isomorphism classes over each object
of the site: on the left because the inclusion is fully faithful, on the right because the
sections of a subfunctor of `yoneda` of a terminal object form a subsingleton. The isomorphism
classes correspond because `P` holds at `y T` exactly when the base change has an object over
`T`. -/
theorem nonempty_equivalenceOver_fullSubcategoryBaseChange
    (hy : y ⋙ 𝒳.val.val.p = Over.map V.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (fullSubcategoryBased 𝒳 P).p 𝒳.val.val.p y
        (fullSubcategoryBasedInclusion 𝒳 P).toFunctor)
      (presheafOfCategories
        ((fullSubcategoryBaseChangeSubfunctor 𝒳 hP y).toFunctor ⋙ typeToCat)).p) := by
  set p := TwoFibreProductOver.fst (Over.map V.hom) (fullSubcategoryBased 𝒳 P).p
    𝒳.val.val.p y (fullSubcategoryBasedInclusion 𝒳 P).toFunctor
  have : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Full := ObjectProperty.full_ι P
  have : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Faithful := ObjectProperty.faithful_ι P
  have hrfl : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor ⋙ 𝒳.val.val.p =
      (fullSubcategoryBased 𝒳 P).p := rfl
  have hgroup : p.IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap V.hom (fullSubcategoryBased 𝒳 P).p 𝒳.val.val.p y
      (fullSubcategoryBasedInclusion 𝒳 P).toFunctor
      (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP) 𝒳.val.property hy rfl
  have hsetoid : p.IsFiberedInSetoids :=
    ⟨hgroup, fun T => TwoFibreProductOver.fiber_isThin_fst_of_faithful T⟩
  have hsubtarget := subsingleton_fullSubcategoryBaseChangeSubfunctor 𝒳 hP y
  have hsubsource : ∀ T, Subsingleton (p.isoClassPresheaf.obj T) := by
    intro T
    refine ⟨fun c d => ?_⟩
    obtain ⟨A, rfl⟩ := Functor.isoClassMk_surjective c
    obtain ⟨C, rfl⟩ := Functor.isoClassMk_surjective d
    obtain ⟨f⟩ := TwoFibreProductOver.nonempty_fst_fiber_hom_of_full_fiber
      (Over.map V.hom) (fullSubcategoryBased 𝒳 P).p 𝒳.val.val.p y
      (fullSubcategoryBasedInclusion 𝒳 P).toFunctor hrfl
      (fun W => Functor.Fiber.full_mapOfComp hrfl W) A C
    have : IsIso f := (hgroup.fiber_isGroupoid T.unop).all_isIso f
    exact Functor.isoClassMk_eq_of_iso (asIso f)
  refine exists_equivalenceOver_elements_of_setoids p _ (fun T => ?_) ?_
  · exact
      { toFun := fun c => ⟨Over.mkIdTerminal.from T.unop, by
          obtain ⟨A, -⟩ := Functor.isoClassMk_surjective c
          exact prop_of_fullSubcategoryBaseChange_fibre 𝒳 hP y T.unop A⟩
        invFun := fun s => Functor.isoClassMk p
          (fullSubcategoryBaseChangeFibre 𝒳 y hy T.unop s.2)
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  · exact fun _ _ _ _ => Subsingleton.elim _ _

include hP in
/-- **Representability of a full-subcategory inclusion by algebraic spaces, given algebraicity of
the subfunctor.** The Stacks 02ZW condition on the inclusion of the full subcategory cut out by a
property inherited along morphisms holds as soon as every
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` is an algebraic space over the
scheme it lives over.

The representing presheaf asked for by Stacks 02ZW is that subfunctor, and the equivalence over
the site is `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`. The
algebraicity hypothesis is the only remaining input. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion
    (halg : ∀ (W : BigFppfOver B S hS)
      (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
      (_hz : z ⋙ 𝒳.val.val.p = Over.map W.hom),
      IsAlgebraicSpace B W.left.1 W.left.2
        (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z).toFunctor) :
    IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) := by
  intro W _ _ z hz
  exact ⟨_, halg W z hz, nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hP z hz⟩

/-! ### The property cut out by a set of points -/

variable (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))

/-- The property of an object `x` of an algebraic stack that every field-valued point admitting a
morphism to `x` represents a point of `Ω`.

For `x` lying over an object `T` of the site this is the condition that the image of `|T|` in
`|𝒳|` under the 1-morphism named by `x` lie in `Ω`: a field-valued point of `𝒳` with a morphism
to `x` is the same datum as a field-valued point of `T` together with a lift of it along `x`. -/
def pointsWithin : ObjectProperty 𝒳.val.val.obj :=
  fun x => ∀ (q : FieldValuedPoint B S hS 𝒳.val.val) (_ : q.obj ⟶ x),
    pointClass B S hS 𝒳.val.val 𝒳.val.property q ∈ Ω

/-- `AlgebraicGeometry.Stack.pointsWithin` is inherited along morphisms: a field-valued point
mapping to the source of a morphism also maps to its target. -/
theorem pointsWithin_of_hom {a b : 𝒳.val.val.obj} (f : a ⟶ b) :
    pointsWithin 𝒳 Ω b → pointsWithin 𝒳 Ω a :=
  fun hb q φ => hb q (φ ≫ f)

/-- **The base change of the inclusion of the full subcategory cut out by a set of points.** For
the property `AlgebraicGeometry.Stack.pointsWithin` of a set `Ω` of points of `|𝒳|`, the base
change of the inclusion along a scheme-valued point with values in `V` is the category of
elements of the subfunctor of `yoneda V` whose sections over `T` are present exactly when every
point of `|𝒳|` seen by `y T` lies in `Ω`. -/
theorem nonempty_equivalenceOver_fullSubcategoryBaseChange_pointsWithin
    (hy : y ⋙ 𝒳.val.val.p = Over.map V.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom)
        (fullSubcategoryBased 𝒳 (pointsWithin 𝒳 Ω)).p 𝒳.val.val.p y
        (fullSubcategoryBasedInclusion 𝒳 (pointsWithin 𝒳 Ω)).toFunctor)
      (presheafOfCategories ((fullSubcategoryBaseChangeSubfunctor 𝒳
        (fun f => pointsWithin_of_hom 𝒳 Ω f) y).toFunctor ⋙ typeToCat)).p) :=
  nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳
    (fun f => pointsWithin_of_hom 𝒳 Ω f) y hy

end AlgebraicGeometry.Stack

end
