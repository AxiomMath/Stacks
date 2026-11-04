module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of an action of a group object

`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/BaseChange.lean` builds the group
algebraic space `G_B = B ×_S G` attached to a group scheme `G` over `S` belonging to the big
fppf site, in two steps: `CategoryTheory.grpObjCompForget` turns the functor of points of `G`
restricted to the site into a group object of presheaves of sets, and
`CategoryTheory.overProdFstGrpObj` turns that into a group object `B ⨯ P` of the slice over `B`.
This file supplies the module half of each step.

An object `Y` of a category `C` with binary products acted on by a group object `P` gives
`B ⨯ Y`, over `B`, acted on by `B ⨯ P`, with the action on the points over an object `Z` over
`B` the action of `Z.left ⟶ P` on `Z.left ⟶ Y`.  Dually, a group object `M` of a category `E`
acting on an object `Q` of `E` gives the presheaf of points `X ↦ (J.obj X ⟶ Q)` on a category
`D` mapping to `E`, acted on pointwise by the presheaf of groups `X ↦ (J.obj X ⟶ M)`.  Together
they carry an action of a group scheme of the big fppf site on a scheme of that site to the
action of `G_B = B ×_S G` on `B ×_S Q` over `B`, which is the datum Stacks 044Q, part (2),
consumes.

## Main definitions

* `CategoryTheory.overProdFstFunctor`: the functor `W ↦ (B ⨯ W → B)` from `C` to the slice over
  `B`, with `CategoryTheory.overProdFstAdj` the adjunction exhibiting it as a right adjoint of
  `CategoryTheory.Over.forget`.
* `CategoryTheory.overProdFstModObj`: the module-object structure on `B ⨯ Y` over `B ⨯ P`.
* `CategoryTheory.opCompYoneda`: the Yoneda embedding of `E` restricted along a functor
  `J : D ⥤ E`, taking `Q` to the presheaf `X ↦ (J.obj X ⟶ Q)` on `D`, with
  `CategoryTheory.opCompYonedaObjIso` identifying the presheaf of points of `J.obj a` with the
  presheaf represented by `a` when `J` is fully faithful.
* `CategoryTheory.opCompYonedaModObj`: the module-object structure on that presheaf of points
  over the presheaf of groups `X ↦ (J.obj X ⟶ M)`.
* `AlgebraicGeometry.Space.pointsOnSiteModObj` and
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteModObj`: the module
  counterparts of `AlgebraicGeometry.Space.pointsOnSite` and of
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`, over the very group objects
  those two carry.

## Main results

* `CategoryTheory.overProdFst_ε_comp_map_one` and
  `CategoryTheory.overProdFst_μ_comp_map_mul`: the unit and the multiplication of
  `CategoryTheory.overProdFstGrpObj` are the images of those of `P` under the lax monoidal
  structure of `CategoryTheory.overProdFstFunctor`.  These are what let the generic transport
  `CategoryTheory.Functor.LaxMonoidal.modObj` be taken over the group object the library already
  has, rather than over a second one.  `CategoryTheory.opCompYoneda_ε_comp_map_one` and
  `CategoryTheory.opCompYoneda_μ_comp_map_mul` are the same two equations for
  `CategoryTheory.grpObjCompForget` at a restricted Yoneda embedding.
* `CategoryTheory.overProdFst_smul_left_comp_snd`: the action of
  `CategoryTheory.overProdFstModObj` on points is the pointwise action, read through the second
  projection.  This pins the transported action down, so that it is the action of `P` on `Y` and
  not a twist of it.  `CategoryTheory.opCompYoneda_smul_app` does the same for
  `CategoryTheory.opCompYonedaModObj`: the action on the sections over an object `X` of `D` is
  the action of `J.obj X ⟶ M` on `J.obj X ⟶ Q` in `E`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_prod_toSchemeOverYoneda`: the product of an
  algebraic space with the functor of points on the site of a scheme coming from the site is an
  algebraic space, so the acted-on object above satisfies the algebraicity hypothesis of
  Stacks 044Q, part (2).

## Implementation notes

Mathlib's `CategoryTheory.Over.star` is the same functor as
`CategoryTheory.overProdFstFunctor`, but it is built from the cofree comonad coalgebra and its
value on an object does not reduce to `Over.mk (prod.fst : B ⨯ W ⟶ B)`.  That reduction is what
is needed here: the module structure has to be stated on the very object that
`CategoryTheory.overProdFstGrpObj` carries the group structure on, so that the two can be handed
to a consumer together.  `CategoryTheory.overProdFstFunctor` is therefore written with that
object map, and `CategoryTheory.overProdFstAdj` records that it is still a right adjoint of the
forgetful functor, which is where its preservation of finite products — and hence its monoidal
structure — comes from.  `CategoryTheory.opCompYoneda` is written for the same reason as the
composite of `CategoryTheory.yoneda` with whiskering along `J.op`: its value on an object
reduces to `J.op ⋙ yoneda.obj Q`, which is what
`AlgebraicGeometry.Space.pointsOnSite` composed with the forgetful functor is, so that one
`CategoryTheory.grpObjCompForget` serves both; and its preservation of finite products is then
that of the two factors.

Both transports are `CategoryTheory.Functor.LaxMonoidal.modObj`, whose target monoid structure
is a parameter; the four equations above identify that parameter with the group structure the
library already has.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryProducts C]

/-! ### The functor `B ⨯ -` into the slice over `B` -/

/-- The functor taking an object `W` of `C` to the product `B ⨯ W`, viewed over `B` through its
first projection. -/
@[reducible]
noncomputable def overProdFstFunctor (B : C) : C ⥤ Over B where
  obj W := Over.mk (prod.fst : B ⨯ W ⟶ B)
  map f := Over.homMk (prod.lift prod.fst (prod.snd ≫ f)) (by simp)
  map_id _ := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp
  map_comp _ _ := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp

omit [CartesianMonoidalCategory C] in
/-- The underlying object of `(overProdFstFunctor B).obj W` is `B ⨯ W`. -/
@[simp] theorem overProdFstFunctor_obj_left (B W : C) :
    ((overProdFstFunctor B).obj W).left = (B ⨯ W) := rfl

omit [CartesianMonoidalCategory C] in
/-- The structure morphism of `(overProdFstFunctor B).obj W` is the first projection. -/
@[simp] theorem overProdFstFunctor_obj_hom (B W : C) :
    ((overProdFstFunctor B).obj W).hom = prod.fst := rfl

omit [CartesianMonoidalCategory C] in
/-- The underlying morphism of `(overProdFstFunctor B).map f` is
`prod.lift prod.fst (prod.snd ≫ f)`. -/
@[simp] theorem overProdFstFunctor_map_left (B : C) {W W' : C} (f : W ⟶ W') :
    ((overProdFstFunctor B).map f).left = prod.lift prod.fst (prod.snd ≫ f) := rfl

/-- `CategoryTheory.Over.forget` is left adjoint to `CategoryTheory.overProdFstFunctor`: a
morphism from `Z` to `B ⨯ W` over `B` is a morphism `Z.left ⟶ W`. -/
noncomputable def overProdFstAdj (B : C) : Over.forget B ⊣ overProdFstFunctor B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z W =>
        { toFun := fun x => Over.homMk (prod.lift Z.hom x) (by simp)
          invFun := fun x => x.left ≫ prod.snd
          left_inv _ := by simp
          right_inv := by
            intro x
            apply Over.OverMorphism.ext
            apply prod.hom_ext
            · simpa using (Over.w x).symm
            · simp }
      homEquiv_naturality_left_symm := by intro Z' Z W f g; simp
      homEquiv_naturality_right := by
        intro Z W W' f g
        apply Over.OverMorphism.ext
        apply prod.hom_ext <;> simp }

/-- `CategoryTheory.overProdFstFunctor B` is a right adjoint. -/
noncomputable instance (B : C) : (overProdFstFunctor B).IsRightAdjoint :=
  ⟨_, ⟨overProdFstAdj B⟩⟩

omit [CartesianMonoidalCategory C] in
/-- Two morphisms into `B ⨯ W` over `B` agree as soon as their second projections do. -/
theorem overProdFst_hom_ext {B W : C} {Z : Over B}
    {h₁ h₂ : Z ⟶ Over.mk (prod.fst : B ⨯ W ⟶ B)}
    (h : h₁.left ≫ prod.snd = h₂.left ≫ prod.snd) : h₁ = h₂ :=
  Over.OverMorphism.ext (prod.hom_ext ((Over.w h₁).trans (Over.w h₂).symm) h)

section Monoidal

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts

variable (B : C) [CartesianMonoidalCategory (Over B)]

/-- The lax monoidal comparison of `CategoryTheory.overProdFstFunctor`, read on points: a pair of
morphisms to `B ⨯ W` and to `B ⨯ W'` over `B` goes to the pair of their second projections. -/
theorem overProdFst_lift_comp_μ_left_comp_snd {W W' : C} {Z : Over B}
    (g : Z ⟶ Over.mk (prod.fst : B ⨯ W ⟶ B)) (x : Z ⟶ Over.mk (prod.fst : B ⨯ W' ⟶ B)) :
    (lift g x ≫ Functor.LaxMonoidal.μ (overProdFstFunctor B) W W').left ≫ prod.snd =
      lift (g.left ≫ prod.snd) (x.left ≫ prod.snd) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · have h : ((lift g x ≫ Functor.LaxMonoidal.μ (overProdFstFunctor B) W W') ≫
        (overProdFstFunctor B).map (fst W W')).left ≫ prod.snd = g.left ≫ prod.snd := by
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
    simpa using h
  · have h : ((lift g x ≫ Functor.LaxMonoidal.μ (overProdFstFunctor B) W W') ≫
        (overProdFstFunctor B).map (snd W W')).left ≫ prod.snd = x.left ≫ prod.snd := by
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    simpa using h

variable (P : C) [GrpObj P]

/-- The unit of `CategoryTheory.overProdFstGrpObj` is the image of the unit of `P`. -/
theorem overProdFst_ε_comp_map_one :
    Functor.LaxMonoidal.ε (overProdFstFunctor B) ≫ (overProdFstFunctor B).map η[P] =
      η[Over.mk (prod.fst : B ⨯ P ⟶ B)] := by
  apply overProdFst_hom_ext
  have hone : (1 : 𝟙_ (Over B) ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)) =
      η[Over.mk (prod.fst : B ⨯ P ⟶ B)] := by
    rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over B))) (𝟙 _), Category.id_comp]
  have key := map_one (overProdFstHomMulEquiv B P (𝟙_ (Over B)))
  rw [overProdFstHomMulEquiv_apply, hone, Hom.one_def] at key
  rw [key, Over.comp_left, overProdFstFunctor_map_left, Category.assoc, prod.lift_snd,
    ← Category.assoc, toUnit_unique
      ((Functor.LaxMonoidal.ε (overProdFstFunctor B)).left ≫ prod.snd)
      (toUnit ((𝟙_ (Over B)).left))]

/-- The multiplication of `CategoryTheory.overProdFstGrpObj` is the image of the multiplication
of `P`. -/
theorem overProdFst_μ_comp_map_mul :
    Functor.LaxMonoidal.μ (overProdFstFunctor B) P P ≫ (overProdFstFunctor B).map μ[P] =
      μ[Over.mk (prod.fst : B ⨯ P ⟶ B)] := by
  apply overProdFst_hom_ext
  have hmul : (fst (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B))) *
      (snd (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B))) =
        μ[Over.mk (prod.fst : B ⨯ P ⟶ B)] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have key := map_mul (overProdFstHomMulEquiv B P
    (Over.mk (prod.fst : B ⨯ P ⟶ B) ⊗ Over.mk (prod.fst : B ⨯ P ⟶ B)))
    (fst (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B)))
    (snd (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B)))
  rw [overProdFstHomMulEquiv_apply, overProdFstHomMulEquiv_apply, overProdFstHomMulEquiv_apply,
    hmul, Hom.mul_def] at key
  rw [key, Over.comp_left, overProdFstFunctor_map_left, Category.assoc, prod.lift_snd,
    ← Category.assoc, ← overProdFst_lift_comp_μ_left_comp_snd B
      (fst (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B)))
      (snd (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ P ⟶ B))),
    lift_fst_snd, Category.id_comp]

variable (Y : C) [ModObj P Y]

/-- The module-object structure on `B ⨯ Y` over `B ⨯ P` in the slice over `B`, induced by an
action of `P` on `Y`.  This is the module counterpart of
`CategoryTheory.overProdFstGrpObj`. -/
noncomputable instance overProdFstModObj :
    ModObj (Over.mk (prod.fst : B ⨯ P ⟶ B)) (Over.mk (prod.fst : B ⨯ Y ⟶ B)) :=
  Functor.LaxMonoidal.modObj (overProdFstFunctor B) (M := P) (X := Y)
    (GrpObj.toMonObj (self := overProdFstGrpObj B P))
    (overProdFst_ε_comp_map_one B P) (overProdFst_μ_comp_map_mul B P)

/-- The action morphism of `CategoryTheory.overProdFstModObj` is the image of the action
morphism of `P` on `Y`. -/
theorem overProdFst_smul_eq :
    γ[Over.mk (prod.fst : B ⨯ P ⟶ B), Over.mk (prod.fst : B ⨯ Y ⟶ B)] =
      Functor.LaxMonoidal.μ (overProdFstFunctor B) P Y ≫
        (overProdFstFunctor B).map γ[P, Y] :=
  rfl

/-- The action of `CategoryTheory.overProdFstModObj` on the points over an object `Z` over `B`
is the action of `Z.left ⟶ P` on `Z.left ⟶ Y`, read through the second projection. -/
theorem overProdFst_smul_left_comp_snd {Z : Over B}
    (g : Z ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)) (x : Z ⟶ Over.mk (prod.fst : B ⨯ Y ⟶ B)) :
    (g • x).left ≫ prod.snd = (g.left ≫ prod.snd) • (x.left ≫ prod.snd) := by
  rw [Hom.smul_def, Hom.smul_def, overProdFst_smul_eq, ← Category.assoc,
    ← overProdFst_lift_comp_μ_left_comp_snd B g x]
  simp

end Monoidal

/-! ### The functor of points on a subcategory, as a presheaf module object -/

section OpCompYoneda

variable {D : Type*} [Category.{v} D] {E : Type*} [Category.{v} E]

/-- The Yoneda embedding of `E` restricted along a functor `J : D ⥤ E`: an object `Q` of `E`
goes to the presheaf `X ↦ (J.obj X ⟶ Q)` on `D`. -/
@[reducible, sga "4 Vbis 2.3.1.1" "more general"]
def opCompYoneda (J : D ⥤ E) : E ⥤ (Dᵒᵖ ⥤ Type v) :=
  yoneda ⋙ (Functor.whiskeringLeft Dᵒᵖ Eᵒᵖ (Type v)).obj J.op

/-- `CategoryTheory.opCompYoneda` acts on morphisms by composition. -/
theorem opCompYoneda_map_app (J : D ⥤ E) {Q Q' : E} (f : Q ⟶ Q') (X : Dᵒᵖ)
    (g : (J.op ⋙ yoneda.obj Q).obj X) :
    ((opCompYoneda J).map f).app X g = g ≫ f :=
  rfl

/-- A fully faithful `J` identifies the presheaf of points of `J.obj a` on `D` with the presheaf
represented by `a`. -/
def opCompYonedaObjIso {J : D ⥤ E} (hJ : J.FullyFaithful) (a : D) :
    yoneda.obj a ≅ (opCompYoneda J).obj (J.obj a) :=
  NatIso.ofComponents (fun _ => Equiv.toIso hJ.homEquiv)
    (fun f => by ext g; exact J.map_comp f.unop g)

section Module

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts

variable [CartesianMonoidalCategory E] (J : D ⥤ E)

/-- The lax monoidal comparison of `CategoryTheory.opCompYoneda`, read on points: a pair of
morphisms out of `J.obj X` goes to the morphism into the product that the two of them define. -/
theorem opCompYoneda_μ_app (Q Q' : E) (X : Dᵒᵖ) (f : J.obj X.unop ⟶ Q)
    (g : J.obj X.unop ⟶ Q') :
    (Functor.LaxMonoidal.μ (opCompYoneda J) Q Q').app X (f, g) = lift f g := by
  refine hom_ext _ _ ?_ ?_
  · exact congr($(Functor.Monoidal.μ_fst (opCompYoneda J) Q Q').app X (f, g)).trans
      (lift_fst _ _).symm
  · exact congr($(Functor.Monoidal.μ_snd (opCompYoneda J) Q Q').app X (f, g)).trans
      (lift_snd _ _).symm

variable (M : E) [GrpObj M]

/-- The unit of the presheaf of groups `X ↦ (J.obj X ⟶ M)`, that is of
`CategoryTheory.grpObjCompForget` at the restricted Yoneda embedding, is the image of the unit
of `M`. -/
@[ega "0 8.2.7" "special case"]
theorem opCompYoneda_ε_comp_map_one :
    Functor.LaxMonoidal.ε (opCompYoneda J) ≫ (opCompYoneda J).map η[M] =
      η[(J.op ⋙ yonedaGrpObj M) ⋙ forget GrpCat] := by
  ext X x
  show (Functor.LaxMonoidal.ε (opCompYoneda J)).app X x ≫ η[M] = (1 : J.obj X.unop ⟶ M)
  rw [Hom.one_def]
  congr 1
  exact toUnit_unique _ _

/-- The multiplication of the presheaf of groups `X ↦ (J.obj X ⟶ M)` is the image of the
multiplication of `M`. -/
theorem opCompYoneda_μ_comp_map_mul :
    Functor.LaxMonoidal.μ (opCompYoneda J) M M ≫ (opCompYoneda J).map μ[M] =
      μ[(J.op ⋙ yonedaGrpObj M) ⋙ forget GrpCat] := by
  ext X z
  exact congrArg (· ≫ μ[M]) (opCompYoneda_μ_app J M M X z.1 z.2)

variable (Q : E) [ModObj M Q]

/-- The presheaf of points `X ↦ (J.obj X ⟶ Q)` on `D`, as a module object over the presheaf of
groups `X ↦ (J.obj X ⟶ M)`, induced by an action of the group object `M` of `E` on `Q`.  This
is the module counterpart of `CategoryTheory.grpObjCompForget` at a restricted Yoneda
embedding. -/
noncomputable instance opCompYonedaModObj :
    ModObj ((J.op ⋙ yonedaGrpObj M) ⋙ forget GrpCat) (J.op ⋙ yoneda.obj Q) :=
  Functor.LaxMonoidal.modObj (opCompYoneda J) (M := M) (X := Q)
    (GrpObj.toMonObj (self := grpObjCompForget (J.op ⋙ yonedaGrpObj M)))
    (opCompYoneda_ε_comp_map_one J M) (opCompYoneda_μ_comp_map_mul J M)

/-- The action morphism of `CategoryTheory.opCompYonedaModObj` is the image of the action
morphism of `M` on `Q`. -/
theorem opCompYoneda_smul_eq :
    γ[(J.op ⋙ yonedaGrpObj M) ⋙ forget GrpCat, J.op ⋙ yoneda.obj Q] =
      Functor.LaxMonoidal.μ (opCompYoneda J) M Q ≫ (opCompYoneda J).map γ[M, Q] :=
  rfl

/-- The action of `CategoryTheory.opCompYonedaModObj` on the sections over an object `X` of `D`
is the action of `J.obj X ⟶ M` on `J.obj X ⟶ Q` in `E`. -/
theorem opCompYoneda_smul_app (X : Dᵒᵖ) (m : J.obj X.unop ⟶ M) (x : J.obj X.unop ⟶ Q) :
    γ[(J.op ⋙ yonedaGrpObj M) ⋙ forget GrpCat, J.op ⋙ yoneda.obj Q].app X (m, x) = m • x := by
  rw [Hom.smul_def, ← opCompYoneda_μ_app J M Q X m x]
  rfl

end Module

end OpCompYoneda

end CategoryTheory

namespace AlgebraicGeometry.Space

open CategoryTheory

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The big fppf site over `S` sits fully faithfully in the slice of all schemes over `S`: this
is `AlgebraicGeometry.Space.toSchemeOver` read as a fully faithful functor. -/
noncomputable def toSchemeOverFullyFaithful : (toSchemeOver 𝒞 S hS).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful 𝒞.inclusion).over (X := 𝒞.obj hS)

/-- The functor of points on the site of a scheme over `S` that comes from the site is the
presheaf represented by that object of the site.  This is
`AlgebraicGeometry.Space.pointsOnSiteRepresentableBy` without the group structure. -/
noncomputable def toSchemeOverYonedaObjIso (a : BigFppfOver 𝒞 S hS) :
    yoneda.obj a ≅ (toSchemeOver 𝒞 S hS).op ⋙ yoneda.obj ((toSchemeOver 𝒞 S hS).obj a) :=
  opCompYonedaObjIso (toSchemeOverFullyFaithful 𝒞 S hS) a

/-- The product of an algebraic space over `S` with the functor of points on the site of a
scheme coming from the site is an algebraic space over `S`: it is the restriction of the first
factor to that object of the site. -/
theorem isAlgebraicSpace_prod_toSchemeOverYoneda
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    (a : BigFppfOver 𝒞 S hS) :
    IsAlgebraicSpace 𝒞 S hS
      (B ⨯ ((toSchemeOver 𝒞 S hS).op ⋙ yoneda.obj ((toSchemeOver 𝒞 S hS).obj a))) :=
  isAlgebraicSpace_of_iso 𝒞 S hS
    ((prod.mapIso (Iso.refl B) (toSchemeOverYonedaObjIso 𝒞 S hS a).symm).trans
      (prod.braiding B (yoneda.obj a)))
    (isAlgebraicSpace_prod_yoneda_obj a hB)

/-- The module counterpart of `AlgebraicGeometry.Space.pointsOnSite`: an action of a group
scheme `G` over `S` belonging to the big fppf site on a scheme `Q` over `S` restricts to an
action of the presheaf of groups `pointsOnSite` on the functor of points of `Q`, pointwise on
the site. -/
@[instance_reducible, ega "II 8.3.9" "Direction"]
noncomputable def pointsOnSiteModObj (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (Q : Over S)
    (hQ : letI := hG; ModObj ((toSchemeOver 𝒞 S hS).obj G) Q) :
    ModObj (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat)
      ((toSchemeOver 𝒞 S hS).op ⋙ yoneda.obj Q) :=
  letI := hG
  letI := hQ
  opCompYonedaModObj (toSchemeOver 𝒞 S hS) ((toSchemeOver 𝒞 S hS).obj G) Q

/-- The module counterpart of
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`: for an action of a group
scheme `G` over `S` belonging to the big fppf site on a scheme `Q` over `S`, the group algebraic
space `G_B = B ×_S G` over an algebraic space `B` acts on `B ×_S Q` over `B`, through the group
object `ofGroupSchemeInSite` carries. -/
@[instance_reducible]
noncomputable def GroupAlgebraicSpace.ofGroupSchemeInSiteModObj
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (Q : Over S)
    (hQ : letI := hG; ModObj ((toSchemeOver 𝒞 S hS).obj G) Q) :
    ModObj (Over.mk (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B))
      (Over.mk (prod.fst : B ⨯ ((toSchemeOver 𝒞 S hS).op ⋙ yoneda.obj Q) ⟶ B)) :=
  letI := pointsOnSiteModObj 𝒞 S hS G hG Q hQ
  overProdFstModObj B (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat)
    ((toSchemeOver 𝒞 S hS).op ⋙ yoneda.obj Q)

end AlgebraicGeometry.Space

end
