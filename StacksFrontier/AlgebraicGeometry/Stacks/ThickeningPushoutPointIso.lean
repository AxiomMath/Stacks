module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# The 2-Yoneda points of an object of a two-fibre product of fibres

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids with a choice of pullbacks, let `f : X ⟶ Y` and
`i : X ⟶ X'` be morphisms of `𝒞`, and let `y` over `Y`, `x'` over `X'` be objects together with an
isomorphism `α : f^* y ≅ i^* x'` of the fibre over `X` — an object of the two-fibre product of the
fibres over `Y` and `X'` over the fibre over `X`, as in Stacks 07WN. The 2-Yoneda lemma
(Stacks 004B) attaches to `y` and `x'` the functors `𝒞/Y ⥤ 𝒳` and `𝒞/X' ⥤ 𝒳` of their chosen
lifts (`CategoryTheory.Functor.TwoYoneda.liftFunctor`). This file shows that `α` makes the two
composites `𝒞/X ⥤ 𝒳`, through `f` and through `i`, isomorphic by an isomorphism vertical over
the base: at `h : T ⟶ X` the lift of `y` along `h ≫ f` and the lift of `x'` along `h ≫ i` are
both pullbacks of the common object `f^* y ≅ i^* x'` along `h`.

## Main definitions

* `AlgebraicGeometry.Stack.ThickeningPushout.pointCompIso`: the natural isomorphism
  `Over.map f ⋙ liftFunctor y ≅ Over.map i ⋙ liftFunctor x'`.

## Main results

* `AlgebraicGeometry.Stack.ThickeningPushout.pointCompHom_fac`: the component at `h`, followed by
  the chosen lift of `x'` along `h ≫ i`, is the factorisation of the chosen lift of `y` along
  `h ≫ f` through `f^* y`, followed by `α` and the chosen lift `i^* x' ⟶ x'`.
* `AlgebraicGeometry.Stack.ThickeningPushout.isHomLift_pointCompHom`: the components are
  vertical.
* `AlgebraicGeometry.Stack.ThickeningPushout.pointCompHom_naturality`: the components are natural
  in the object of the slice.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.ThickeningPushout

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒞)
  (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)

/-- The structure morphism of an object of a slice, typed with its source written as the
underlying object. Phrasing lifts with this morphism keeps the implicit objects of
`CategoryTheory.Functor.IsHomLift` syntactically uniform, which instance search requires. -/
def ovHom {X : 𝒞} (h : Over X) : h.left ⟶ X := h.hom

/-- `ovHom` of the slice object `Over.mk g` is `g`. -/
@[simp] lemma ovHom_mk {T X : 𝒞} (g : T ⟶ X) : ovHom (Over.mk g) = g := rfl

/-- The chosen cartesian morphism from the value of the 2-Yoneda point of `y` at `a` to `y`. -/
noncomputable def liftπ {Y : 𝒞} (y : p.Fiber Y) (a : Over Y) :
    (TwoYoneda.liftFunctor p hp Y y).obj a ⟶ y.1 :=
  (TwoYoneda.chosenLift p hp Y y a).φ

/-- The chosen lift of `y` at an object of the slice lies over its structure morphism. -/
lemma isStronglyCartesian_liftπ {Y : 𝒞} (y : p.Fiber Y) (a : Over Y) :
    p.IsStronglyCartesian (ovHom a) (liftπ p hp y a) :=
  (TwoYoneda.chosenLift p hp Y y a).isStronglyCartesian

/-- The chosen lift of `y` at `(Over.map f).obj h` lies over `h ≫ f`. -/
lemma isStronglyCartesian_liftπ_map {X Y : 𝒞} (f : X ⟶ Y) (y : p.Fiber Y) (h : Over X) :
    p.IsStronglyCartesian (ovHom h ≫ f) ((liftπ p hp y ((Over.map f).obj h))) :=
  (TwoYoneda.chosenLift p hp Y y ((Over.map f).obj h)).isStronglyCartesian

/-- The 2-Yoneda point carries a morphism of the slice to the factorisation of the chosen lifts. -/
@[reassoc (attr := simp)]
lemma liftFunctor_map_liftπ {U : 𝒞} (x : p.Fiber U) {a a' : Over U} (m : a ⟶ a') :
    (TwoYoneda.liftFunctor p hp U x).map m ≫ liftπ p hp x a' = liftπ p hp x a := by
  rw [TwoYoneda.liftFunctor_map]
  exact @IsStronglyCartesian.fac _ _ _ _ p _ _ _ _ a'.hom (TwoYoneda.chosenLift p hp U x a').φ
    (TwoYoneda.chosenLift p hp U x a').isStronglyCartesian _ _ _ _ (Over.w m).symm _
    (TwoYoneda.chosenLift p hp U x a).isStronglyCartesian.toIsHomLift

variable {X X' Y : 𝒞} (f : X ⟶ Y) (i : X ⟶ X') (y : p.Fiber Y) (x' : p.Fiber X')
  (α : c.obj f y ≅ c.obj i x')

/-- The factorisation through `f^* y ⟶ y` of the chosen lift of `y` along `h ≫ f`; it lies over
`h`. -/
noncomputable def pointFactor (h : Over X) :
    (TwoYoneda.liftFunctor p hp Y y).obj ((Over.map f).obj h) ⟶ (c.obj f y).1 :=
  have := isStronglyCartesian_liftπ_map p hp f y h
  IsStronglyCartesian.map p f (c.map f y) (f' := ovHom h ≫ f) (g := ovHom h) rfl
    (liftπ p hp y ((Over.map f).obj h))

/-- `pointFactor` lies over the structure morphism of `h`. -/
lemma isHomLift_pointFactor (h : Over X) : p.IsHomLift (ovHom h) (pointFactor p hp c f y h) := by
  have := isStronglyCartesian_liftπ_map p hp f y h
  unfold pointFactor; infer_instance

/-- `pointFactor` followed by the chosen lift `f^* y ⟶ y` is the chosen lift of `y` along `h ≫ f`.
-/
@[reassoc (attr := simp)]
lemma pointFactor_fac (h : Over X) :
    pointFactor p hp c f y h ≫ c.map f y =
      (liftπ p hp y ((Over.map f).obj h)) := by
  have := isStronglyCartesian_liftπ_map p hp f y h
  exact IsStronglyCartesian.fac p f (c.map f y) (f' := ovHom h ≫ f) (g := ovHom h) rfl _

/-- The morphism from the lift of `y` along `h ≫ f` to `x'` through `α`; it lies over `h ≫ i`. -/
noncomputable def pointTransfer (h : Over X) :
    (TwoYoneda.liftFunctor p hp Y y).obj ((Over.map f).obj h) ⟶ x'.1 :=
  pointFactor p hp c f y h ≫ α.hom.1 ≫ c.map i x'

/-- `pointTransfer` lies over `h ≫ i`. -/
lemma isHomLift_pointTransfer (h : Over X) :
    p.IsHomLift (ovHom h ≫ i) (pointTransfer p hp c f i y x' α h) := by
  have : p.IsHomLift (𝟙 X) (α.hom.1) := α.hom.2
  have := isHomLift_pointFactor p hp c f y h
  have : p.IsHomLift i (c.map i x') := (c.isStronglyCartesian i x').toIsHomLift
  have : p.IsHomLift i (α.hom.1 ≫ c.map i x') :=
    IsHomLift.comp_lift_id_left' p X _ i _
  exact IsHomLift.comp p (ovHom h) i _ _

/-- The component at `h : T ⟶ X` of the comparison: the unique morphism over `𝟙 T` from the lift
of `y` along `h ≫ f` to the lift of `x'` along `h ≫ i` compatible with `α`. -/
noncomputable def pointCompHom (h : Over X) :
    (TwoYoneda.liftFunctor p hp Y y).obj ((Over.map f).obj h) ⟶
      (TwoYoneda.liftFunctor p hp X' x').obj ((Over.map i).obj h) :=
  have := isStronglyCartesian_liftπ_map p hp i x' h
  have := isHomLift_pointTransfer p hp c f i y x' α h
  IsStronglyCartesian.map p (ovHom h ≫ i)
    (liftπ p hp x' ((Over.map i).obj h))
    (f' := ovHom h ≫ i) (g := 𝟙 h.left) (Category.id_comp _).symm
    (pointTransfer p hp c f i y x' α h)

/-- The component `pointCompHom` at `h` is vertical: it lies over the identity of `h.left`. -/
lemma isHomLift_pointCompHom (h : Over X) :
    p.IsHomLift (𝟙 h.left) (pointCompHom p hp c f i y x' α h) := by
  have := isStronglyCartesian_liftπ_map p hp i x' h
  have := isHomLift_pointTransfer p hp c f i y x' α h
  unfold pointCompHom; infer_instance

/-- The component `pointCompHom` at `h`, followed by the chosen lift of `x'` along `h ≫ i`, is
`pointTransfer`. -/
@[reassoc (attr := simp)]
lemma pointCompHom_fac (h : Over X) :
    pointCompHom p hp c f i y x' α h ≫
        (liftπ p hp x' ((Over.map i).obj h)) =
      pointTransfer p hp c f i y x' α h := by
  have := isStronglyCartesian_liftπ_map p hp i x' h
  have := isHomLift_pointTransfer p hp c f i y x' α h
  exact IsStronglyCartesian.fac p (ovHom h ≫ i) _ (f' := ovHom h ≫ i) (g := 𝟙 h.left)
    (Category.id_comp _).symm _

/-! ### Naturality -/

omit c in
/-- The 2-Yoneda point, precomposed with `Over.map f`, carries `m` to a morphism lying over
`m.left`. -/
lemma isHomLift_liftFunctor_map_overMap {h h' : Over X} (m : h' ⟶ h) :
    p.IsHomLift m.left ((TwoYoneda.liftFunctor p hp Y y).map ((Over.map f).map m)) := by
  have : (Over.forget Y).IsHomLift m.left ((Over.map f).map m) :=
    IsHomLift.of_fac' _ m.left _ rfl rfl (by simp)
  exact isHomLift_map_of_comp_eq (TwoYoneda.liftFunctor_w p hp Y y) m.left _

/-- The factorisation through `f^* y` is natural in the object of the slice. -/
@[reassoc]
lemma liftFunctor_map_pointFactor {h h' : Over X} (m : h' ⟶ h) :
    (TwoYoneda.liftFunctor p hp Y y).map ((Over.map f).map m) ≫ pointFactor p hp c f y h =
      pointFactor p hp c f y h' := by
  have := isHomLift_liftFunctor_map_overMap p hp f y m
  have := isHomLift_pointFactor p hp c f y h
  have := isHomLift_pointFactor p hp c f y h'
  have : p.IsHomLift (m.left ≫ ovHom h) ((TwoYoneda.liftFunctor p hp Y y).map
      ((Over.map f).map m) ≫ pointFactor p hp c f y h) := inferInstance
  have hm : m.left ≫ ovHom h = ovHom h' := Over.w m
  have : p.IsHomLift (ovHom h') ((TwoYoneda.liftFunctor p hp Y y).map
      ((Over.map f).map m) ≫ pointFactor p hp c f y h) := hm ▸ this
  exact IsStronglyCartesian.ext p f (c.map f y) (ovHom h') (by
    rw [Category.assoc, pointFactor_fac, liftFunctor_map_liftπ, pointFactor_fac])

/-- **The comparison is natural.** -/
@[reassoc]
lemma pointCompHom_naturality {h h' : Over X} (m : h' ⟶ h) :
    pointCompHom p hp c f i y x' α h' ≫
        (TwoYoneda.liftFunctor p hp X' x').map ((Over.map i).map m) =
      (TwoYoneda.liftFunctor p hp Y y).map ((Over.map f).map m) ≫
        pointCompHom p hp c f i y x' α h := by
  have := isStronglyCartesian_liftπ_map p hp i x' h
  have := isHomLift_pointCompHom p hp c f i y x' α h
  have := isHomLift_pointCompHom p hp c f i y x' α h'
  have := isHomLift_liftFunctor_map_overMap p hp f y m
  have := isHomLift_liftFunctor_map_overMap p hp i x' m
  refine IsStronglyCartesian.ext p (ovHom h ≫ i)
    (liftπ p hp x' ((Over.map i).obj h)) m.left ?_
  rw [Category.assoc, liftFunctor_map_liftπ, pointCompHom_fac, Category.assoc, pointCompHom_fac,
    pointTransfer, pointTransfer, liftFunctor_map_pointFactor_assoc]

/-- The comparison is an isomorphism: it is a morphism of a fibre of a category fibred in
groupoids. -/
instance isIso_pointCompHom (h : Over X) : IsIso (pointCompHom p hp c f i y x' α h) :=
  have := isHomLift_pointCompHom p hp c f i y x' α h
  have := hp.isStronglyCartesian_homLift (𝟙 h.left) (pointCompHom p hp c f i y x' α h)
  IsStronglyCartesian.isIso_of_base_isIso p (𝟙 h.left) _

/-- **The isomorphism of 2-Yoneda points over `X` induced by `α`.** -/
noncomputable def pointCompIso :
    Over.map f ⋙ TwoYoneda.liftFunctor p hp Y y ≅ Over.map i ⋙ TwoYoneda.liftFunctor p hp X' x' :=
  NatIso.ofComponents (fun h => asIso (pointCompHom p hp c f i y x' α h))
    (fun m => (pointCompHom_naturality p hp c f i y x' α m).symm)

/-- The component of `pointCompIso` at `h` is `pointCompHom`. -/
@[simp] lemma pointCompIso_hom_app (h : Over X) :
    (pointCompIso p hp c f i y x' α).hom.app h = pointCompHom p hp c f i y x' α h := rfl

end AlgebraicGeometry.Stack.ThickeningPushout

end
