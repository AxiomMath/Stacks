module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctor
public import StacksFrontier.Deformation.Cofibered

/-!
# Fibre categories, pushforwards and choices of pushforwards

Let `p : F ⥤ C` be a category cofibered in groupoids. This file records the notation-fixing
remarks (2)–(6) of Stacks 06GK.

* (2) The fibre category over `U` is Mathlib's `Functor.Fiber p U`: its objects are the objects of
  `F` lying over `U`, and its morphisms are the morphisms of `F` lying over `𝟙 U`
  (`Deformation.fiberHomEquiv`).
* (3) The fibre categories are groupoids (`Deformation.isGroupoid_fiber`), so each carries a
  `Groupoid` structure (`Deformation.fiberGroupoid`).
* (4) A pushforward of `x` along `f : U ⟶ V` is a morphism `x ⟶ y` lying over `f`; it exists
  (`Deformation.exists_pushforward`) and is unique up to unique isomorphism
  (`Deformation.existsUnique_iso_of_isHomLift`).
* (5) A choice of pushforwards (`Deformation.ChoiceOfPushforwards`) exists by the axiom of choice
  (`Deformation.nonempty_choiceOfPushforwards`).
* (6) A choice of pushforwards gives a pseudofunctor from `C` to categories whose values are the
  fibre groupoids (`Deformation.pushforwardPseudofunctor`).

## Implementation notes

For (6) we reuse the pullback pseudofunctor of the fibred category `p.op : Fᵒᵖ ⥤ Cᵒᵖ`
(`CategoryTheory.Functor.IsFibered.pullbackPseudofunctor`, Stacks 02XO), precomposed with the
pseudofunctor `LocallyDiscrete C ⥤ᵖ LocallyDiscrete Cᵒᵖᵒᵖ` induced by `opOp C`. Its value at `U`
is the fibre of `p.op` over `op U`, whose objects are the objects of `F` lying over `U` and whose
morphisms are the reversed vertical morphisms; it is a groupoid
(`Deformation.isGroupoid_pushforwardPseudofunctor_obj`). The pushforwards it uses are those of the
choice made by `CategoryTheory.Functor.IsPreFibered.pullbackObj` for `p.op`, i.e. the choice of
pushforwards `Deformation.ChoiceOfPushforwards.ofIsFibered`. Stacks gives no details of this
construction.

## References

* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 06SH](https://stacks.math.columbia.edu/tag/06SH)
-/

@[expose] public section

namespace Deformation

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]

/-! ### (2) The fibre categories -/

/-- **Stacks 06GK (2).** The morphisms `x ⟶ y` of the fibre category `p.Fiber U` are exactly the
morphisms of `F` between the underlying objects lying over `𝟙 U`. -/
@[stacks 06GK "(2) the fibre category F(U): objects of F over U, morphisms of F over id_U"]
def fiberHomEquiv (p : F ⥤ C) (U : C) (x y : p.Fiber U) :
    (x ⟶ y) ≃ {φ : x.1 ⟶ y.1 // p.IsHomLift (𝟙 U) φ} where
  toFun φ := ⟨Fiber.fiberInclusion.map φ, φ.2⟩
  invFun φ := ⟨φ.1, φ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### (3) The fibre categories are groupoids -/

/-- **Stacks 06GK (3).** The fibre categories of a category cofibered in groupoids are groupoids:
every morphism of `p.Fiber U` is an isomorphism (Categories, Lemma 003V). -/
@[stacks 06GK "(3) the fibre categories F(U) are groupoids"]
theorem isGroupoid_fiber {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) (U : C) :
    IsGroupoid (p.Fiber U) := by
  refine ⟨fun {x y} φ ↦ ?_⟩
  let φ₀ : x.1 ⟶ y.1 := Fiber.fiberInclusion.map φ
  have hφ₀ : p.IsHomLift (𝟙 U) φ₀ := φ.2
  have : IsIso φ₀ := isIso_of_isHomLift_id hp φ₀ hφ₀
  let ψ : y ⟶ x := ⟨inv φ₀, inferInstance⟩
  refine ⟨ψ, Fiber.hom_ext ?_, Fiber.hom_ext ?_⟩
  · exact IsIso.hom_inv_id φ₀
  · exact IsIso.inv_hom_id φ₀

/-- **Stacks 06GK (3).** The groupoid structure on a fibre category of a category cofibered in
groupoids. -/
@[stacks 06GK "(3) the fibre category F(U) as a groupoid"]
noncomputable abbrev fiberGroupoid {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) (U : C) :
    Groupoid (p.Fiber U) :=
  letI := isGroupoid_fiber hp U
  Groupoid.ofIsGroupoid

/-! ### (4) Pushforwards are unique up to unique isomorphism -/

/-- **Stacks 06GK (4).** Two pushforwards `a : x ⟶ y` and `a' : x ⟶ y'` of `x` along `f : U ⟶ V`
(morphisms lying over `f`) differ by a unique isomorphism `y ≅ y'` lying over `𝟙 V` and
compatible with `a` and `a'`. -/
@[stacks 06GK "(4) a pushforward is unique up to unique isomorphism"]
theorem existsUnique_iso_of_isHomLift {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) {U V : C}
    (f : U ⟶ V) {x y y' : F} (a : x ⟶ y) (a' : x ⟶ y') [p.IsHomLift f a] [p.IsHomLift f a'] :
    ∃! e : y ≅ y', p.IsHomLift (𝟙 V) e.hom ∧ a ≫ e.hom = a' := by
  have : p.IsStronglyCocartesian f a := isStronglyCocartesian_of_isCofiberedInGroupoids hp f a
    inferInstance
  have : p.IsStronglyCocartesian f a' := isStronglyCocartesian_of_isCofiberedInGroupoids hp f a'
    inferInstance
  refine ⟨IsCocartesian.codomainUniqueUpToIso p f a a', ⟨?_, ?_⟩, ?_⟩
  · exact IsCocartesian.map_isHomLift p f a a'
  · exact IsCocartesian.fac p f a a'
  · rintro e ⟨he, hea⟩
    apply Iso.ext
    exact IsCocartesian.map_uniq p f a a' e.hom hea

/-! ### (5) Choices of pushforwards -/

/-- **Stacks 06GK (5).** A *choice of pushforwards* for `p`: for every morphism `f : U ⟶ V` of
`C` and every object `x` of the fibre over `U`, an object `obj f x` of the fibre over `V` and a
pushforward `hom f x : x ⟶ obj f x` of `x` along `f`. -/
@[stacks 06GK "(5) a choice of pushforwards"]
structure ChoiceOfPushforwards (p : F ⥤ C) where
  /-- The chosen pushforward `f_* x` of `x` along `f`. -/
  obj : ∀ {U V : C} (_ : U ⟶ V), p.Fiber U → p.Fiber V
  /-- The chosen arrow `x ⟶ f_* x`. -/
  hom : ∀ {U V : C} (f : U ⟶ V) (x : p.Fiber U), x.1 ⟶ (obj f x).1
  /-- The chosen arrow lies over `f`. -/
  isHomLift : ∀ {U V : C} (f : U ⟶ V) (x : p.Fiber U), p.IsHomLift f (hom f x)

/-- The choice of pushforwards made by the axiom of choice, through `Deformation.pushforwardObj`
and `Deformation.chosenPushforwardMap`. -/
noncomputable def ChoiceOfPushforwards.ofIsCofiberedInGroupoids {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) : ChoiceOfPushforwards p where
  obj f x := ⟨pushforwardObj hp f x.1 x.2, pushforwardObj_eq hp f x.1 x.2⟩
  hom f x := chosenPushforwardMap hp f x.1 x.2
  isHomLift f x := chosenPushforwardMap_lift hp f x.1 x.2

/-- **Stacks 06GK (5).** A category cofibered in groupoids admits a choice of pushforwards,
by the axiom of choice. -/
@[stacks 06GK "(5) a choice of pushforwards exists by the axiom of choice"]
theorem nonempty_choiceOfPushforwards {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) :
    Nonempty (ChoiceOfPushforwards p) :=
  ⟨ChoiceOfPushforwards.ofIsCofiberedInGroupoids hp⟩

/-- The choice of pushforwards underlying the cleaving of the fibred category `p.op` chosen by
`CategoryTheory.Functor.IsPreFibered.pullbackObj`: the pushforward of `x` along `f` is the source
of the chosen cartesian lift of `f.op` with target `op x`. -/
noncomputable def ChoiceOfPushforwards.ofIsFibered (p : F ⥤ C) [p.op.IsFibered] :
    ChoiceOfPushforwards p where
  obj f x := ⟨(IsPreFibered.pullbackObj (p := p.op) (a := Opposite.op x.1)
    (congrArg Opposite.op x.2) f.op).unop,
      congrArg Opposite.unop (IsPreFibered.pullbackObj_proj (p := p.op)
        (congrArg Opposite.op x.2) f.op)⟩
  hom f x := (IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x.1)
    (congrArg Opposite.op x.2) f.op).unop
  isHomLift f _ := isHomLift_unop p f.op _

/-! ### (6) The associated pseudofunctor -/

/-- **Stacks 06GK (6).** The pseudofunctor `C → Groupoids` associated to a category cofibered in
groupoids together with the choice of pushforwards `ChoiceOfPushforwards.ofIsFibered p`. Its
value at `U` is the fibre of `p.op` over `op U` (the objects of `F` over `U`, a groupoid by
`isGroupoid_pushforwardPseudofunctor_obj`), and its value at `f : U ⟶ V` is pushforward along `f`.
It is the pullback pseudofunctor of the fibred category `p.op` (Stacks 02XO), reindexed along
`opOp C`. -/
@[stacks 06GK "(6) the pseudofunctor C → Groupoids attached to a choice of pushforwards"]
noncomputable def pushforwardPseudofunctor {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) :
    Pseudofunctor (LocallyDiscrete C) Cat :=
  letI : p.op.IsFibered := IsFiberedInGroupoids.isFibered hp
  (opOp C).toPseudofunctor.comp (IsFibered.pullbackPseudofunctor p.op)

/-- The value of the pseudofunctor of a category cofibered in groupoids at `U` is the fibre of
`p.op` over `op U`. -/
theorem pushforwardPseudofunctor_obj {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) (U : C) :
    (pushforwardPseudofunctor hp).obj ⟨U⟩ = Cat.of (p.op.Fiber (Opposite.op U)) :=
  rfl

/-- On a morphism `f : U ⟶ V`, the pseudofunctor of a category cofibered in groupoids sends an
object `x` over `U` to its chosen pushforward along `f`. -/
theorem pushforwardPseudofunctor_map_obj {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) {U V : C}
    (f : U ⟶ V) (x : p.op.Fiber (Opposite.op U)) :
    letI : p.op.IsFibered := IsFiberedInGroupoids.isFibered hp
    ((pushforwardPseudofunctor hp).map (⟨f⟩ : (⟨U⟩ : LocallyDiscrete C) ⟶ ⟨V⟩)).toFunctor.obj x =
      ⟨Opposite.op ((ChoiceOfPushforwards.ofIsFibered p).obj f ⟨x.1.unop,
        congrArg Opposite.unop x.2⟩).1,
        congrArg Opposite.op ((ChoiceOfPushforwards.ofIsFibered p).obj f ⟨x.1.unop,
          congrArg Opposite.unop x.2⟩).2⟩ :=
  rfl

/-- The values of the pseudofunctor of a category cofibered in groupoids are groupoids. -/
@[stacks 06GK "(6) the values of the pseudofunctor are groupoids"]
theorem isGroupoid_pushforwardPseudofunctor_obj {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    (U : C) : IsGroupoid ((pushforwardPseudofunctor hp).obj ⟨U⟩) :=
  IsFiberedInGroupoids.fiber_isGroupoid hp (Opposite.op U)

end Deformation
