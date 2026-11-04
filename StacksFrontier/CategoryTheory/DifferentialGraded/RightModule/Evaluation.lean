module

public import StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.RestrictionExact
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda

/-!
# Evaluation at an object, as a functor to modules over its endomorphism complex

Let `C` be a differential graded category over a commutative ring `R` and let `K` be an object
of `C`. Write `E = C(K, K)` for the one-object differential graded subcategory on `K` of
`StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismDGCategory`. *Evaluation at `K`* is
restriction along the inclusion `E ⥤ C`:

`ev_K : Mod^dg(C) ⥤ Mod^dg(E)`, `(ev_K M)(∗) = M(K)`.

A right differential graded `C`-module `M` has, at the object `K`, a complex `M(K)` on which
the homogeneous morphisms of `C(K, K)` already act — that action is a restriction of the
action of `C` which is part of the datum of `M`. Evaluation at `K` records exactly that
complex with exactly that action: nothing is reconstructed from the underlying complex of
abelian groups, and the acting object is `C(K, K)` itself and not another algebra built from
it. This is the content of `DGCategory.evaluation_obj_act`.

Applied to the representable module `h_X = C(-, X)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda`, evaluation at `K` gives
the complex `C(K, X)` with `C(K, K)` acting by composition in `C`; the resulting functor of
differential graded categories `C ⥤ Mod^dg(E)` is the functor `X ↦ Hom(K, X)` of
[Stacks, Tag 09LE] appearing in [Stacks, Tag 09LK].

## Main definitions

* `DGCategory.DGFunctor.comp`: the composite of two functors of differential graded
  categories.
* `DGCategory.evaluationDGFunctor`: `ev_K : Mod^dg(C) ⥤ Mod^dg(E)`.
* `DGCategory.evaluationOnK`: the induced functor `K(Mod^dg(C)) ⥤ K(Mod^dg(E))`.
* `DGCategory.homDGFunctor`: the composite `X ↦ C(K, X)`, from `C` to `Mod^dg(E)`.

## Main results

* `DGCategory.evaluation_obj`, `DGCategory.evaluation_obj_d` and
  `DGCategory.evaluation_obj_act`: the value of `ev_K M` at the single object is `M(K)`, with
  the differential of `M` and with `f : C(K, K)` acting as it acts on `M`.
* `DGCategory.isTriangulated_evaluationOnK`: `ev_K` is exact on the homotopy categories.
* `DGCategory.homDGFunctor_obj_obj` and `DGCategory.homDGFunctor_obj_act`: the value of the
  composite at `X` is the complex `C(K, X)` with `C(K, K)` acting by composition in `C`.
* `DGCategory.DGFunctor.onK_comp`: the functor induced on homotopy categories by a composite
  is the composite of the induced functors.

## Implementation notes

Evaluation is not a new construction: it is `DGCategory.restrictDGFunctor` at the inclusion
`DGCategory.endDGInclusion`, so its exactness is
`DGCategory.isTriangulated_restrictOnK` and every computation of its values is a reflexivity.
Keeping it an `abbrev` is what makes those reflexivities available to a reader who has only
the evaluation in scope.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ r

open CategoryTheory

variable {R : Type r} [CommRing R]

/-! ### Composing functors of differential graded categories -/

/-- The composite of two functors of differential graded categories. -/
def DGFunctor.comp {A : DGCategory.{v₁, u₁} R} {B : DGCategory.{v₂, u₂} R}
    {D : DGCategory.{v₃, u₃} R} (F : DGFunctor A B) (G : DGFunctor B D) : DGFunctor A D where
  obj x := G.obj (F.obj x)
  map := fun {_ _ _} f => G.map (F.map f)
  map_add := fun {_ _ _} f g => by rw [F.map_add, G.map_add]
  map_smul := fun {_ _ _} c f => by rw [F.map_smul, G.map_smul]
  map_d := fun {_ _ _} f => by rw [F.map_d, G.map_d]
  map_comp := fun {_ _ _ _ _ _} h g f => by rw [F.map_comp, G.map_comp]
  map_id := fun x => by rw [F.map_id, G.map_id]

/-- The composite `F.comp G` sends an object `x` of `A` to `G.obj (F.obj x)`. -/
@[simp] theorem DGFunctor.comp_obj {A : DGCategory.{v₁, u₁} R} {B : DGCategory.{v₂, u₂} R}
    {D : DGCategory.{v₃, u₃} R} (F : DGFunctor A B) (G : DGFunctor B D) (x : A.Obj) :
    (F.comp G).obj x = G.obj (F.obj x) := rfl

/-- The composite `F.comp G` sends a homogeneous morphism `f` of `A` to `G.map (F.map f)`. -/
@[simp] theorem DGFunctor.comp_map {A : DGCategory.{v₁, u₁} R} {B : DGCategory.{v₂, u₂} R}
    {D : DGCategory.{v₃, u₃} R} (F : DGFunctor A B) (G : DGFunctor B D) {x y : A.Obj} {n : ℤ}
    (f : A.Hom x y n) : (F.comp G).map f = G.map (F.map f) := rfl

/-- **The homotopy category functor of a composite is the composite of the functors.** -/
theorem DGFunctor.onK_comp {A : DGCategory.{v₁, u₁} R} {B : DGCategory.{v₂, u₂} R}
    {D : DGCategory.{v₃, u₃} R} (F : DGFunctor A B) (G : DGFunctor B D) :
    (F.comp G).onK = F.onK ⋙ G.onK :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ f =>
    Quotient.inductionOn f fun _ => HEq.rfl

/-! ### Evaluation at an object -/

variable (C : DGCategory.{v, u} R) (K : C.Obj)

/-- **Evaluation at `K`**: restriction of right differential graded `C`-modules along the
inclusion of the one-object differential graded subcategory `E = C(K, K)`, as a functor of
differential graded categories `Mod^dg(C) ⥤ Mod^dg(E)`. The value of `ev_K M` at the single
object of `E` is the complex `M(K)`, and `C(K, K)` acts on it by the action of `M`. -/
abbrev evaluationDGFunctor :
    DGFunctor (rightModuleCategory.{w} C) (rightModuleCategory.{w} (endDGCategory C K)) :=
  restrictDGFunctor.{w} (endDGInclusion C K)

/-- The degree-`i` part of `ev_K M` is the degree-`i` part of `M` at `K`. -/
@[simp] theorem evaluation_obj (M : RightModule.{w} C) (e : (endDGCategory C K).Obj) (i : ℤ) :
    ((evaluationDGFunctor.{w} C K).obj M).obj e i = M.obj K i := rfl

/-- The differential of `ev_K M` is the differential of `M` at `K`. -/
@[simp] theorem evaluation_obj_d (M : RightModule.{w} C) {e : (endDGCategory C K).Obj}
    {i j : ℤ} (h : i + 1 = j) (a : M.obj K i) :
    ((evaluationDGFunctor.{w} C K).obj M).d (x := e) h a = M.d h a := rfl

/-- **The `E`-action on `ev_K M` is the action of `M`.** A homogeneous morphism of
`E = C(K, K)` is a homogeneous endomorphism of `K` in `C`, and it acts on `M(K)` by the right
action of `M` on that very morphism. No action is reconstructed, and the acting object is
`C(K, K)` itself. -/
@[simp] theorem evaluation_obj_act (M : RightModule.{w} C) {e e' : (endDGCategory C K).Obj}
    {m n k : ℤ} (h : m + n = k) (a : M.obj K m) (f : C.Hom K K n) :
    ((evaluationDGFunctor.{w} C K).obj M).act (x := e) (y := e') h a f = M.act h a f := rfl

/-- The value of `ev_K` on a homogeneous morphism of right differential graded `C`-modules is
that morphism, evaluated at `K`. -/
@[simp] theorem evaluation_map_app {M N : RightModule.{w} C} {p : ℤ}
    (φ : (rightModuleCategory.{w} C).Hom M N p) {e : (endDGCategory C K).Obj} {i j : ℤ}
    (h : i + p = j) (a : M.obj K i) :
    RightModule.app ((evaluationDGFunctor.{w} C K).map φ) (x := e) h a =
      RightModule.app φ h a := rfl

/-- **Evaluation at `K` on the homotopy categories**,
`K(Mod^dg(C)) ⥤ K(Mod^dg(C(K, K)))`. -/
abbrev evaluationOnK :
    (rightModuleCategory.{w} C).K ⥤ (rightModuleCategory.{w} (endDGCategory C K)).K :=
  (evaluationDGFunctor.{w} C K).onK

/-- **Evaluation at `K` is exact.** -/
theorem isTriangulated_evaluationOnK : (evaluationOnK.{w} C K).IsTriangulated :=
  isTriangulated_restrictOnK.{w} (endDGInclusion C K)

/-! ### The representable case: `Hom(K, -)` -/

/-- **The functor `X ↦ Hom(K, X)` of [Stacks, Tag 09LE]**: the differential graded Yoneda
functor `X ↦ h_X = C(-, X)` followed by evaluation at `K`. Its value at `X` is the complex
`C(K, X)`, a right differential graded module over `E = C(K, K)` for the composition of
`C`. -/
def homDGFunctor : DGFunctor C (rightModuleCategory.{v} (endDGCategory C K)) :=
  (yonedaDGFunctor C).comp (evaluationDGFunctor.{v} C K)

/-- The complex underlying `Hom(K, X)` is `C(K, X)`. -/
@[simp] theorem homDGFunctor_obj_obj (X : C.Obj) (e : (endDGCategory C K).Obj) (i : ℤ) :
    ((homDGFunctor C K).obj X).obj e i = C.Hom K X i := rfl

/-- **The `E`-action on `Hom(K, X)` is composition in `C`.** -/
@[simp] theorem homDGFunctor_obj_act (X : C.Obj) {e e' : (endDGCategory C K).Obj}
    {m n k : ℤ} (h : m + n = k) (a : C.Hom K X m) (f : C.Hom K K n) :
    ((homDGFunctor C K).obj X).act (x := e) (y := e') h a f = C.comp h a f := rfl

/-- The functor induced by `Hom(K, -)` on homotopy categories is the differential graded
Yoneda functor followed by evaluation at `K`. -/
theorem homDGFunctor_onK :
    (homDGFunctor C K).onK = (yonedaDGFunctor C).onK ⋙ evaluationOnK.{v} C K :=
  DGFunctor.onK_comp _ _

end DGCategory
