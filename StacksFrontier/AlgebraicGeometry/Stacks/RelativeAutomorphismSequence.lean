module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# The exact sequence of automorphism sheaves of a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `T` be a scheme of that site and let `x` be an object of the fibre category of
`𝒳` over `T`. Write `y = f(x)` for its image in the fibre category of `𝒴` over `T`. Applying `f`
to a local automorphism of `x` gives a local automorphism of `y`, so there is a map of sheaves of
groups on the big fppf site of `T`

`Isom_𝒳(x, x) ⟶ Isom_𝒴(y, y)`

and the local automorphisms `α` of `x` with `f(α) = id` — that is, the sections of the *relative*
automorphism sheaf `Isom_{𝒳/𝒴}(x, x)` — form a subsheaf of groups of `Isom_𝒳(x, x)`. The
sequence

`0 ⟶ Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x) ⟶ Isom_𝒴(y, y)`

is exact: the first map is injective and a section of `Isom_𝒳(x, x)` lies in its image exactly
when its image in `Isom_𝒴(y, y)` is the identity.

The sheaves `Isom_𝒳(x, y)` are `AlgebraicGeometry.Stack.isomSpace`: presheaves on the big fppf
site of `T` whose sections over `V ⟶ T` are the isomorphisms between the restrictions of `x` and
`y` to `V`. The map of sheaves is the restriction to the isomorphisms of the map of morphism
presheaves `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, which applies `f` to a
section and conjugates by the comparison isomorphisms between the chosen pullbacks of `x` and of
`f(x)`.

## Main definitions

* `AlgebraicGeometry.Stack.isFibredOneMorphism_basedFunctor`: a 1-morphism of categories fibred
  in groupoids over the base is a 1-morphism of fibred categories.
* `AlgebraicGeometry.Stack.imageFiberObj`: the image `f(x)` of an object of a fibre category.
* `AlgebraicGeometry.Stack.isomSpaceMap`: the map `Isom_𝒳(x, y) ⟶ Isom_𝒴(f(x), f(y))`.
* `AlgebraicGeometry.Stack.relativeIsomSubfunctor` and
  `AlgebraicGeometry.Stack.relativeIsomSpace`: the relative automorphism sheaf
  `Isom_{𝒳/𝒴}(x, x)`, as a subsheaf of `Isom_𝒳(x, x)` and as a sheaf in its own right.
* `AlgebraicGeometry.Stack.relativeIsomSpaceGrpObj`: its group structure, again composition of
  local automorphisms.

## Main results

* `AlgebraicGeometry.Stack.isMonHom_isomSpaceMap` and
  `AlgebraicGeometry.Stack.isMonHom_relativeIsomSpaceι`: both maps of the sequence are
  homomorphisms of sheaves of groups.
* `AlgebraicGeometry.Stack.relativeIsomSpaceι_app_injective`: the first map is injective.
* `AlgebraicGeometry.Stack.relativeIsom_exact`: exactness in the middle, i.e. the image of the
  first map is the kernel of the second.
* `AlgebraicGeometry.Stack.isomSpaceMap_app_val_eq_id_iff`: a section of `Isom_𝒳(x, x)` is killed
  by the second map exactly when `f` carries it to the identity.

## References

* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 0CPJ](https://stacks.math.columbia.edu/tag/0CPJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Stack

/-- Conjugating an endomorphism by an isomorphism gives the identity exactly when the
endomorphism is the identity. -/
private theorem conj_eq_id_iff {C : Type*} [Category C] {a b : C} (e : a ≅ b) (g : b ⟶ b) :
    e.hom ≫ g ≫ e.inv = 𝟙 a ↔ g = 𝟙 b :=
  ⟨fun h => by simpa using e.inv ≫= h =≫ e.hom, fun h => by simp [h]⟩

section General

variable {𝒞 : Type*} [Category 𝒞] {𝒜 ℬ : Type*} [Category.{u} 𝒜] [Category.{u} ℬ]
  {p : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {G : 𝒜 ⥤ ℬ} [p.IsFibered] [r.IsFibered]

/-- The map of morphism presheaves induced by a 1-morphism of fibred categories carries the
identity section to the identity section. -/
private theorem morPresheafMap_app_id (hG : Functor.IsFibredOneMorphism p r G) {W : 𝒞}
    (a : p.Fiber W) (g : (Over W)ᵒᵖ) :
    (hG.morPresheafMap a a).app g (𝟙 (p.pullbackFiber a g.unop.hom)) = 𝟙 _ := by
  rw [Functor.IsFibredOneMorphism.morPresheafMap_app]
  simp

/-- The map of morphism presheaves induced by a 1-morphism of fibred categories respects
composition of sections. -/
private theorem morPresheafMap_app_comp (hG : Functor.IsFibredOneMorphism p r G) {W : 𝒞}
    (a : p.Fiber W) (g : (Over W)ᵒᵖ)
    (m n : p.pullbackFiber a g.unop.hom ⟶ p.pullbackFiber a g.unop.hom) :
    (hG.morPresheafMap a a).app g (m ≫ n) =
      (hG.morPresheafMap a a).app g m ≫ (hG.morPresheafMap a a).app g n := by
  rw [Functor.IsFibredOneMorphism.morPresheafMap_app,
    Functor.IsFibredOneMorphism.morPresheafMap_app,
    Functor.IsFibredOneMorphism.morPresheafMap_app, CategoryTheory.Functor.map_comp]
  simp

end General

/-- A morphism into a presheaf of types whose sections all lie in a subfunctor factors through
that subfunctor. -/
def subfunctorLift {D : Type*} [Category D] {X P : D ⥤ Type u}
    (G : Subfunctor X) (φ : P ⟶ X) (h : ∀ (V : D) (z : P.obj V), φ.app V z ∈ G.obj V) :
    P ⟶ G.toFunctor where
  app V := TypeCat.ofHom fun z => ⟨φ.app V z, h V z⟩
  naturality _ _ i := by
    ext z
    apply Subtype.ext
    exact NatTrans.naturality_apply φ i z

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (F : 𝒳.val ⥤ᵇ 𝒴.val) (U : BigFppfOver B S hS)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site is a 1-morphism of
fibred categories. -/
theorem isFibredOneMorphism_basedFunctor :
    Functor.IsFibredOneMorphism 𝒳.val.p 𝒴.val.p F.toFunctor where
  comp_eq := F.w
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have := h
    have : 𝒴.val.p.IsHomLift f (F.toFunctor.map φ) :=
      Functor.isHomLift_map_of_comp_eq F.w f φ
    exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift f (F.toFunctor.map φ)

/-- The image `f(x)` of an object of the fibre category of `𝒳` over `U`, as an object of the
fibre category of `𝒴` over `U`. -/
abbrev imageFiberObj (x : 𝒳.val.p.Fiber U) : 𝒴.val.p.Fiber U :=
  (Functor.fiberFunctorOfCompEq (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).comp_eq U).obj x

/-- The object of the category of schemes over `U` attached to a scheme `V` of the big fppf site
of `U`. -/
abbrev sliceObj (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) : Over U :=
  ((Over.iteratedSliceBackward U).op.obj V).unop

/-- The functor induced by `f` on the fibre categories over an object of the big fppf site. -/
abbrev fibreFunctor (W : BigFppfOver B S hS) : 𝒳.val.p.Fiber W ⥤ 𝒴.val.p.Fiber W :=
  Functor.fiberFunctorOfCompEq (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).comp_eq W

/-- The map `Isom_𝒳(x, y) ⟶ Isom_𝒴(f(x), f(y))` on presheaves of isomorphisms over `𝒞/U`,
the restriction of the map of morphism presheaves induced by `f`. -/
def isomPresheafMap (x y : 𝒳.val.p.Fiber U) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
    𝒳.val.p.isomPresheaf x y ⟶
      𝒴.val.p.isomPresheaf (imageFiberObj B S hS 𝒳 𝒴 F U x)
        (imageFiberObj B S hS 𝒳 𝒴 F U y) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  exact
  { app := fun g => TypeCat.ofHom fun m =>
      ⟨((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap x y).app g m.1, by
        have hm : IsIso m.1 :=
          (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) x y m.1).mp m.2
        have hiso : IsIso
            (((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap x y).app g m.1) := by
          rw [Functor.IsFibredOneMorphism.morPresheafMap_app]
          infer_instance
        exact (Functor.mem_isomSubpresheaf_obj (p := 𝒴.val.p) (U := U) _ _ _).mpr hiso⟩
    naturality _ _ h := by
      ext m
      apply Subtype.ext
      exact NatTrans.naturality_apply
        ((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap x y) h m.1 }

/-- The map `Isom_𝒳(x, y) ⟶ Isom_𝒴(f(x), f(y))` of sheaves on the big fppf site of `U` induced
by a 1-morphism `f : 𝒳 ⟶ 𝒴`: it applies `f` to a local isomorphism and compares the chosen
pullbacks of `x` and `y` with those of their images. -/
@[stacks 0CPJ "the map Isom_𝒳(x, x) → Isom_𝒴(y, y)"]
def isomSpaceMap (x y : 𝒳.val.p.Fiber U) :
    isomSpace B S hS 𝒳 U x y ⟶
      isomSpace B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U x)
        (imageFiberObj B S hS 𝒳 𝒴 F U y) :=
  Functor.whiskerLeft (Over.iteratedSliceBackward U).op
    (isomPresheafMap B S hS 𝒳 𝒴 F U x y)

/-- A local automorphism of `x` is killed by the map to `Isom_𝒴(y, y)` exactly when `f` carries
it to the identity. -/
theorem isomSpaceMap_app_val_eq_id_iff (x : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (m : (isomSpace B S hS 𝒳 U x x).obj V) :
    ((isomSpaceMap B S hS 𝒳 𝒴 F U x x).app V m).1 = 𝟙 _ ↔
      (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map m.1 = 𝟙 _ := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  exact conj_eq_id_iff
    ((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).mapPullbackFiberIso x
      (sliceObj B S hS U V).hom)
    ((fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map m.1)

/-- The relative automorphism sheaf `Isom_{𝒳/𝒴}(x, x)`, as a subsheaf of `Isom_𝒳(x, x)`: its
sections over `V` are the local automorphisms `α` of `x` with `f(α) = id`. -/
@[stacks 0CPJ "the sheaf Isom_{𝒳/𝒴}(x, x)"]
def relativeIsomSubfunctor (x : 𝒳.val.p.Fiber U) :
    Subfunctor (isomSpace B S hS 𝒳 U x x) where
  obj V := {m | (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map m.1 = 𝟙 _}
  map {V₁ V₂} i m hm := by
    have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
    have hker : ((isomSpaceMap B S hS 𝒳 𝒴 F U x x).app V₁ m).1 = 𝟙 _ :=
      (isomSpaceMap_app_val_eq_id_iff B S hS 𝒳 𝒴 F U x V₁ m).2 hm
    refine (isomSpaceMap_app_val_eq_id_iff B S hS 𝒳 𝒴 F U x V₂ _).1 ?_
    rw [NatTrans.naturality_apply (isomSpaceMap B S hS 𝒳 𝒴 F U x x) i m]
    change Functor.morRestrict 𝒴.val.p _ _ _ ((isomSpaceMap B S hS 𝒳 𝒴 F U x x).app V₁ m).1 = _
    rw [hker, Functor.morRestrict_id_hom]

/-- The relative automorphism sheaf `Isom_{𝒳/𝒴}(x, x)`, as a sheaf on the big fppf site of `U` in
its own right. -/
abbrev relativeIsomSpace (x : 𝒳.val.p.Fiber U) :
    (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u :=
  (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).toFunctor

/-- The group structure on `Isom_{𝒳/𝒴}(x, x)`, restricted from that of `Isom_𝒳(x, x)`. -/
@[stacks 0CPJ "the group structure on Isom_{𝒳/𝒴}(x, x)", instance_reducible]
def relativeIsomSpaceGrpObj (x : 𝒳.val.p.Fiber U) :
    GrpObj (relativeIsomSpace B S hS 𝒳 𝒴 F U x) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  letI : GrpObj (isomSpace B S hS 𝒳 U x x) := isomSpaceGrpObj B S hS 𝒳 U x
  exact
  { one := subfunctorLift (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x)
      η[isomSpace B S hS 𝒳 U x x] (by
        intro V z
        change (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map (𝟙 _) = 𝟙 _
        exact CategoryTheory.Functor.map_id _ _)
    mul := subfunctorLift (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x)
      (((relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι ⊗ₘ
        (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι) ≫ μ[isomSpace B S hS 𝒳 U x x]) (by
        intro V z
        obtain ⟨a, b⟩ := z
        change (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map (b.1.1 ≫ a.1.1) = 𝟙 _
        rw [CategoryTheory.Functor.map_comp, a.2, b.2, Category.comp_id])
    inv := subfunctorLift (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x)
      ((relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι ≫ GrpObj.inv) (by
        intro V a
        have hiso : IsIso a.1.1 :=
          (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) x x a.1.1).mp a.1.2
        change (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U V).left).map
          (CategoryTheory.inv a.1.1) = 𝟙 _
        rw [CategoryTheory.Functor.map_inv]
        exact IsIso.inv_eq_of_hom_inv_id (by rw [a.2]; exact Category.id_comp _))
    one_mul := by
      ext V z
      obtain ⟨⟨⟩, a⟩ := z
      exact Subtype.ext (Subtype.ext (Category.comp_id _))
    mul_one := by
      ext V z
      obtain ⟨a, ⟨⟩⟩ := z
      exact Subtype.ext (Subtype.ext (Category.id_comp _))
    mul_assoc := by
      ext V z
      obtain ⟨⟨a, b⟩, c⟩ := z
      exact Subtype.ext (Subtype.ext (Category.assoc _ _ _).symm)
    left_inv := by
      ext V z
      have hiso : IsIso z.1.1 :=
        (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) x x z.1.1).mp z.1.2
      exact Subtype.ext (Subtype.ext (IsIso.hom_inv_id z.1.1))
    right_inv := by
      ext V z
      have hiso : IsIso z.1.1 :=
        (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) x x z.1.1).mp z.1.2
      exact Subtype.ext (Subtype.ext (IsIso.inv_hom_id z.1.1)) }

/-- The group law of `Isom_{𝒳/𝒴}(x, x)` is composition of local automorphisms, in the order of
`AlgebraicGeometry.Stack.isomSpaceComp`. -/
theorem relativeIsomSpaceGrpObj_mul_val (x : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (a b : (relativeIsomSpace B S hS 𝒳 𝒴 F U x).obj V) :
    letI : GrpObj (relativeIsomSpace B S hS 𝒳 𝒴 F U x) :=
      relativeIsomSpaceGrpObj B S hS 𝒳 𝒴 F U x
    ((μ[relativeIsomSpace B S hS 𝒳 𝒴 F U x]).app V (a, b)).1.1 = b.1.1 ≫ a.1.1 :=
  rfl

/-- The inclusion `Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x)` is a homomorphism of sheaves of groups. -/
@[stacks 0CPJ "the first map is a homomorphism of sheaves of groups"]
theorem isMonHom_relativeIsomSpaceι (x : 𝒳.val.p.Fiber U) :
    letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
    letI : GrpObj (isomSpace B S hS 𝒳 U x x) := isomSpaceGrpObj B S hS 𝒳 U x
    letI : GrpObj (relativeIsomSpace B S hS 𝒳 𝒴 F U x) :=
      relativeIsomSpaceGrpObj B S hS 𝒳 𝒴 F U x
    IsMonHom (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι := by
  have : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  let : GrpObj (isomSpace B S hS 𝒳 U x x) := isomSpaceGrpObj B S hS 𝒳 U x
  let : GrpObj (relativeIsomSpace B S hS 𝒳 𝒴 F U x) :=
    relativeIsomSpaceGrpObj B S hS 𝒳 𝒴 F U x
  exact ⟨by ext V z; rfl, by ext V z; rfl⟩

/-- The map `Isom_𝒳(x, x) ⟶ Isom_𝒴(f(x), f(x))` is a homomorphism of sheaves of groups. -/
@[stacks 0CPJ "the second map is a homomorphism of sheaves of groups"]
theorem isMonHom_isomSpaceMap (x : 𝒳.val.p.Fiber U) :
    letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
    letI : 𝒴.val.p.IsPreFibered := 𝒴.isFiberedInGroupoids.isFibered.toIsPreFibered
    letI : GrpObj (isomSpace B S hS 𝒳 U x x) := isomSpaceGrpObj B S hS 𝒳 U x
    letI : GrpObj (isomSpace B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U x)
        (imageFiberObj B S hS 𝒳 𝒴 F U x)) :=
      isomSpaceGrpObj B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U x)
    IsMonHom (isomSpaceMap B S hS 𝒳 𝒴 F U x x) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  have : 𝒴.val.p.IsPreFibered := 𝒴.isFiberedInGroupoids.isFibered.toIsPreFibered
  let : GrpObj (isomSpace B S hS 𝒳 U x x) := isomSpaceGrpObj B S hS 𝒳 U x
  let : GrpObj (isomSpace B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U x)
      (imageFiberObj B S hS 𝒳 𝒴 F U x)) :=
    isomSpaceGrpObj B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U x)
  constructor
  · ext V z
    exact Subtype.ext (morPresheafMap_app_id (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F) x _)
  · ext V ⟨a, b⟩
    exact Subtype.ext
      (morPresheafMap_app_comp (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F) x _ b.1 a.1)

/-- The inclusion `Isom_{𝒳/𝒴}(x, x) ⟶ Isom_𝒳(x, x)` is injective on sections. -/
@[stacks 0CPJ "injectivity of the first map"]
theorem relativeIsomSpaceι_app_injective (x : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (a b : (relativeIsomSpace B S hS 𝒳 𝒴 F U x).obj V)
    (h : (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι.app V a =
      (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι.app V b) : a = b :=
  Subtype.ext h

/-- The sequence `0 → Isom_{𝒳/𝒴}(x, x) → Isom_𝒳(x, x) → Isom_𝒴(y, y)` is exact at the middle
term: a local automorphism of `x` has identity image in `Isom_𝒴(y, y)` exactly when it comes from
a relative automorphism of `x`. -/
@[stacks 0CPJ "exactness at Isom_𝒳(x, x)"]
theorem relativeIsom_exact (x : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (m : (isomSpace B S hS 𝒳 U x x).obj V) :
    ((isomSpaceMap B S hS 𝒳 𝒴 F U x x).app V m).1 = 𝟙 _ ↔
      ∃ n : (relativeIsomSpace B S hS 𝒳 𝒴 F U x).obj V,
        (relativeIsomSubfunctor B S hS 𝒳 𝒴 F U x).ι.app V n = m :=
  ⟨fun h => ⟨⟨m, (isomSpaceMap_app_val_eq_id_iff B S hS 𝒳 𝒴 F U x V m).1 h⟩, rfl⟩,
    fun ⟨n, hn⟩ => hn ▸ (isomSpaceMap_app_val_eq_id_iff B S hS 𝒳 𝒴 F U x V n.1).2 n.2⟩

end AlgebraicGeometry.Stack

end
