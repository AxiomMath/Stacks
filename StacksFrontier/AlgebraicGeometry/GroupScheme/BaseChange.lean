module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a group scheme

A group scheme over a base scheme `S` is a scheme `G` over `S` together with a multiplication
`m : G ×_S G → G` over `S` making `G(T)` a group for every scheme `T` over `S`; equivalently,
it is a group object in the cartesian monoidal category `Over S` of schemes over `S`. Along a
morphism `f : S' ⟶ S` the fibre product `G_{S'} = G ×_S S'` is a scheme over `S'`, and the
multiplication base changes to a morphism `m_{S'} : G_{S'} ×_{S'} G_{S'} → G_{S'}` over `S'`.
This file proves that `(G_{S'}, m_{S'})` is again a group scheme.

## Main results

* `CategoryTheory.Adjunction.homMulEquiv`: for an adjunction `L ⊣ R` between cartesian monoidal
  categories whose right adjoint `R` preserves finite products, and a monoid object `M`, the
  adjunction bijection `(L.obj T ⟶ M) ≃ (T ⟶ R.obj M)` is multiplicative for the two induced
  multiplications.
* `AlgebraicGeometry.GroupScheme.grpObjPullbackObj` is the base change `G_{S'}` of a group
  scheme `G` over `S`, as a group scheme over `S'`.
* `AlgebraicGeometry.GroupScheme.pointsMulEquiv` is the same statement in the pointwise form
  of the definition of a group scheme: for a scheme `T` over `S'`, composition with the
  projection `G ×_S S' ⟶ G` identifies the group `G_{S'}(T)` with the group `G(T)`.
* `AlgebraicGeometry.GroupScheme.baseChange` is base change as a functor on group schemes.

## References

* [Stacks Project, Tag 022T](https://stacks.math.columbia.edu/tag/022T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory MonObj
open scoped Obj

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) [R.Monoidal] (M : C) [MonObj M] (T : D)

/-- For an adjunction `L ⊣ R` between cartesian monoidal categories whose right adjoint
preserves finite products, and a monoid object `M`, the adjunction bijection
`(L.obj T ⟶ M) ≃ (T ⟶ R.obj M)` is multiplicative: the multiplication on the left is the one
induced by `M`, and the multiplication on the right the one induced by the monoid object
`R.obj M`. -/
def homMulEquiv : (L.obj T ⟶ M) ≃* (T ⟶ R.obj M) where
  __ := adj.homEquiv T M
  map_mul' a b := by
    change adj.homEquiv T M (a * b) = adj.homEquiv T M a * adj.homEquiv T M b
    simp only [Hom.mul_def, adj.homEquiv_unit, Functor.obj.μ_def, Functor.map_comp,
      ← Functor.Monoidal.lift_μ, comp_lift_assoc, Category.assoc]

/-- `homMulEquiv` is the adjunction bijection. -/
@[simp]
lemma homMulEquiv_apply (a : L.obj T ⟶ M) :
    homMulEquiv adj M T a = adj.homEquiv T M a := rfl

/-- The inverse of `homMulEquiv` is the inverse of the adjunction bijection. -/
@[simp]
lemma homMulEquiv_symm_apply (a : T ⟶ R.obj M) :
    (homMulEquiv adj M T).symm a = (adj.homEquiv T M).symm a := rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.GroupScheme

variable {S S' : Scheme.{u}} (f : S' ⟶ S) (G : Over S)

/-- The scheme underlying the base change of `G` along `f : S' ⟶ S` is the fibre product
`G ×_S S'`. -/
lemma pullbackObj_left : ((Over.pullback f).obj G).left = pullback G.hom f := rfl

/-- The base change of `G` along `f : S' ⟶ S` is a scheme over `S'` through the second
projection of `G ×_S S'`. -/
lemma pullbackObj_hom : ((Over.pullback f).obj G).hom = pullback.snd G.hom f := rfl

variable [GrpObj G]

/-- Let `(G, m)` be a group scheme over `S` and `f : S' ⟶ S` a morphism of schemes. The
pullback `(G_{S'}, m_{S'})` is a group scheme over `S'`. -/
@[stacks 022T, sga "3 VIA 0.4" "partial"]
noncomputable instance grpObjPullbackObj : GrpObj ((Over.pullback f).obj G) :=
  Functor.grpObjObj

/-- The multiplication `m_{S'}` of the group scheme `G_{S'}` is the base change of the
multiplication `m` of `G` along `f`. -/
lemma mul_pullbackObj :
    μ[(Over.pullback f).obj G] =
      Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map μ[G] :=
  rfl

/-- In the group of `T`-points of `G_{S'}`, the product of `a b : T ⟶ G_{S'}` is the morphism
`(a, b)` into `G_{S'} ×_{S'} G_{S'}` followed by the base change `m_{S'}` of the multiplication
`m` of `G`. -/
lemma points_mul_eq (T : Over S') (a b : T ⟶ (Over.pullback f).obj G) :
    a * b =
      lift a b ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map μ[G] :=
  rfl

/-- The inverse of the group scheme `G_{S'}` is the base change of the inverse of `G`. -/
lemma inv_pullbackObj : ι[(Over.pullback f).obj G] = (Over.pullback f).map ι[G] := rfl

/-- The identity section of `G_{S'}` is the base change of the identity section of `G`. -/
lemma one_pullbackObj :
    η[(Over.pullback f).obj G] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G] :=
  rfl

/-- For every scheme `T` over `S'`, the pair `(G_{S'}(T), m_{S'})` is a group, and composition
with the projection `G ×_S S' ⟶ G` identifies it with the group `(G(T), m)` of morphisms
`T ⟶ G` over `S`. -/
@[stacks 022T]
noncomputable def pointsMulEquiv (T : Over S') :
    (T ⟶ (Over.pullback f).obj G) ≃* ((Over.map f).obj T ⟶ G) :=
  (Adjunction.homMulEquiv (Over.mapPullbackAdj f) G T).symm

/-- The identification of `G_{S'}(T)` with `G(T)` is composition with the projection
`G ×_S S' ⟶ G`. -/
@[simp]
lemma pointsMulEquiv_apply_left (T : Over S') (a : T ⟶ (Over.pullback f).obj G) :
    (pointsMulEquiv f G T a).left = a.left ≫ pullback.fst G.hom f := by
  simp [pointsMulEquiv, Over.mapPullbackAdj]

/-- Base change of group schemes along `f : S' ⟶ S`, as a functor. On objects it is the
pullback `G ↦ G_{S'}`, and on morphisms it is the base change of a homomorphism of group
schemes over `S`. -/
@[sga "3 XXVI 7.15"]
noncomputable def baseChange : Grp (Over S) ⥤ Grp (Over S') := (Over.pullback f).mapGrp

/-- The scheme over `S'` underlying the base change of `A` is the pullback along `f` of the
scheme over `S` underlying `A`. -/
@[simp]
lemma baseChange_obj_X (A : Grp (Over S)) :
    ((baseChange f).obj A).X = (Over.pullback f).obj A.X :=
  rfl

/-- The morphism over `S'` underlying the base change of a homomorphism of group schemes is
its pullback along `f`. -/
@[simp]
lemma baseChange_map_hom_hom {A B : Grp (Over S)} (φ : A ⟶ B) :
    ((baseChange f).map φ).hom.hom = (Over.pullback f).map φ.hom.hom :=
  rfl

end AlgebraicGeometry.GroupScheme
