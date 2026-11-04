module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints

/-!
# The relative weak assassin of a module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `F` be an
`𝒪_X`-module. A point `x` of `X` belongs to the *relative weak assassin*
`WeakAss_{X/Y}(F) ⊆ |X|` when, for some field-valued representative of the image `f(x)`, the
fibre of `f` over that representative carries a point above `x` which is weakly associated to
the restriction of `F` to the fibre. When the fibres of `f` are locally Noetherian this set is
the one written `Ass_{X/Y}(F)`.

Weak association of a point of an algebraic space is
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`, taken over the étale local ring and the
geometric stalk.

Under the point topology, the set of points of `X` lying over a field-valued point of `Y` is
the image of the points of the fibre, so a specialization of `x` into the fibre is the same
thing as a point of the closure of `{x}` lying over that field-valued point.

## Main definitions

* `AlgebraicGeometry.Space.fibreAtFieldValuedPoint`: the fibre of a morphism of algebraic
  spaces over a field-valued point of its target, an algebraic space.
* `AlgebraicGeometry.Space.fibreAtFieldValuedPointProjection`: its projection to the source.
* `AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint`: membership of a point of `X` in
  `WeakAss_{X/Y}(F)`.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints`: the set `WeakAss_{X/Y}(F)`.

## Main results

* `AlgebraicGeometry.Space.pointsMap_eq_class_of_isRelativeWeaklyAssociatedPoint`: a relative
  weakly associated point is carried by `f` to the class of the field-valued point witnessing
  its membership.
* `AlgebraicGeometry.Space.exists_mem_closure_mem_range_fibre_iff`: the closure of a point
  meets the set of points lying over a field-valued point of `Y` exactly when the point
  specializes to a point lying over it.

## Implementation notes

The fibre of `f` over a field-valued point `p` of `Y` is the presheaf fibre product of `f`
with the morphism `AlgebraicGeometry.Space.fieldMorphism` that `p` presents, which is an
algebraic space by Stacks 02X2. The restriction of `F` to it is the pullback of modules
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU along the projection; that pullback is
available at the module universe of the structure rings only, so the module universe of the
definitions below is that of the schemes.

`AlgebraicGeometry.Space.ImpurityDiagram.IsRelativeWeakAssassinPoint` spells out the same
condition for the single morphism `X_T ⟶ T` of an impurity diagram.
`IsRelativeWeaklyAssociatedPoint` is that condition for an arbitrary morphism of algebraic
spaces.

The description of the points lying over a field-valued point is Stacks 0AC8, in the form
`AlgebraicGeometry.Space.range_pointsMap_fibre_fieldMorphism`: the map on points induced by
the projection from the fibre has image exactly the set of points whose image under `|f|` is
the class of the field-valued point. No decency or finiteness hypothesis enters there.

Stacks 0CUZ gives four further conditions equivalent to the one defined here, phrased on
étale charts rather than on field-valued points: a point of `X` is relatively weakly
associated when, for some — equivalently every — scheme `V` étale over `Y`, scheme `U` étale
over `X ×_Y V`, and compatible points `v` of `V` and `u` of `U`, the point `u` is weakly
associated to the restriction of `F` to `U_v`. Those chart conditions are what transfer the
notion along an étale chart in either direction, and they are stated over the Zariski weak
assassin of the chart scheme rather than over
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a field-valued point of the target -/

/-- The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a field-valued point `p` of
the target: the presheaf fibre product of `f` with the morphism `p` presents, which is an
algebraic space by Stacks 02X2. -/
noncomputable abbrev fibreAtFieldValuedPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) : AlgebraicSpaces B S hS :=
  ⟨Limits.pullback f.hom (fieldMorphism B S hS Y.1 p),
    isAlgebraicSpace_pullback B S hS f.hom (fieldMorphism B S hS Y.1 p) X.2
      (isAlgebraicSpace_yoneda B S hS p.siteObject) Y.2⟩

/-- The projection to the source of `f` from the fibre of `f` over a field-valued point of the
target. -/
noncomputable abbrev fibreAtFieldValuedPointProjection {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y.1) :
    fibreAtFieldValuedPoint B S hS f p ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.fst f.hom (fieldMorphism B S hS Y.1 p))

/-! ### The relative weak assassin -/

/-- A point `x` of `X` lies in the relative weak assassin `WeakAss_{X/Y}(F)` of an `𝒪_X`-module
`F` along a morphism `f : X ⟶ Y` of algebraic spaces: for some field-valued representative of
the image of `x` in `Y`, the fibre of `f` over that representative carries a point above `x`
which is weakly associated to the restriction of `F` to the fibre.

This is condition (5) of Stacks 0CUZ, the field-valued one. When the fibres of `f` are locally
Noetherian — for instance when `f` is locally of finite type, by Stacks 0CUY — this set is
also written `Ass_{X/Y}(F)`. -/
@[stacks 0CV0 "the membership predicate, via condition (5) of 0CUZ; stated for every module,
not only a quasi-coherent one"]
noncomputable def IsRelativeWeaklyAssociatedPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∃ p : FieldValuedPoint B S hS Y.1,
    p.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x ∧
      ∃ θ : points B S hS (fibreAtFieldValuedPoint B S hS f p).1,
        pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
            (fibreAtFieldValuedPointProjection B S hS f p).hom θ = x ∧
          IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
            ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) θ

/-- The relative weak assassin `WeakAss_{X/Y}(F) ⊆ |X|` of an `𝒪_X`-module along a morphism of
algebraic spaces. When the fibres of `f` are locally Noetherian this is the set written
`Ass_{X/Y}(F)`. -/
@[stacks 0CV0 "the set WeakAss_{X/Y}(F), which under locally Noetherian fibres is Ass_{X/Y}(F)"]
noncomputable abbrev relativeWeaklyAssociatedPoints {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) : Set (points B S hS X.1) :=
  {x | IsRelativeWeaklyAssociatedPoint B S hS f F x}

/-- Membership in the relative weak assassin is the relative weak association predicate. -/
@[simp]
theorem mem_relativeWeaklyAssociatedPoints_iff {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) :
    x ∈ relativeWeaklyAssociatedPoints B S hS f F ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  Iff.rfl

/-- A relative weakly associated point is carried by `f` to the class of the field-valued point
witnessing its membership. -/
theorem pointsMap_eq_class_of_isRelativeWeaklyAssociatedPoint {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {F : Modules.{u, u} B S hS X.1 X.2} {x : points B S hS X.1}
    (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x) :
    ∃ p : FieldValuedPoint B S hS Y.1,
      pointsMap B S hS X.1 f.hom x = p.class B S hS Y.1 :=
  ⟨hx.choose, hx.choose_spec.1.symm⟩

/-! ### Specializing into the fibre -/

section Specialization

attribute [local instance] pointTopology

/-- The closure of a point `x'` of `X` meets the set of points lying over a field-valued point
`p` of `Y` exactly when `x'` specializes to a point whose image under `|f|` is the class of
`p`.

The set of points lying over `p` is the image of the points of the fibre of `f` over `p` under
the projection to `X`, by `AlgebraicGeometry.Space.range_pointsMap_fibre_fieldMorphism`
(Stacks 0AC8). -/
theorem exists_mem_closure_mem_range_fibre_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (x' : points B S hS X) :
    (∃ t ∈ closure ({x'} : Set (points B S hS X)),
        t ∈ Set.range (pointsMap B S hS (Limits.pullback f (fieldMorphism B S hS Y p))
          (Limits.pullback.fst f (fieldMorphism B S hS Y p)))) ↔
      ∃ t : points B S hS X, x' ⤳ t ∧ pointsMap B S hS X f t = p.class B S hS Y := by
  rw [range_pointsMap_fibre_fieldMorphism B S hS f p]
  exact ⟨fun ⟨t, ht, hmem⟩ => ⟨t, specializes_iff_mem_closure.mpr ht, hmem⟩,
    fun ⟨t, hspec, hmem⟩ => ⟨t, specializes_iff_mem_closure.mp hspec, hmem⟩⟩

end Specialization

end AlgebraicGeometry.Space

end
