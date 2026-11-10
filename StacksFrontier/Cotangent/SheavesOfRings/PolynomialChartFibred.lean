module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialChart

/-!
# Polynomial charts form a fibred category

For a scheme `X` over a ring `Λ`, the category of polynomial charts of `X` is fibred over the
Zariski category of open subschemes of `X`. A chart `(U ⟶ A)` is pulled back along an inclusion
`V ≤ U` of open subschemes by restricting its arrow to `V` and keeping the same affine space.

## Main results

* `AlgebraicGeometry.PolynomialChart.openFunctor_isFibered`: the forgetful functor from
  polynomial charts to open subschemes is fibred.

## References

* [Stacks Project, Tag 08V9](https://stacks.math.columbia.edu/tag/08V9)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PolynomialChart

noncomputable section

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}
  {structureMap : X ⟶ Spec (CommRingCat.of Λ)}

/-- The restriction of a polynomial chart to a smaller open subscheme, with the same affine
space and the same arrow to it. -/
private def restrict (Q : PolynomialChart Λ X structureMap) (R : X.Opens) (h : R ≤ Q.openPart) :
    PolynomialChart Λ X structureMap where
  openPart := R
  variableIndex := Q.variableIndex
  affineSpace := Q.affineSpace
  affineEquiv := Q.affineEquiv
  toAffine := X.homOfLE h ≫ Q.toAffine
  comm := by
    rw [Category.assoc, Q.comm]
    exact congrArg (fun k => k ≫ structureMap) (X.homOfLE_ι h)

/-- The canonical morphism from a restriction of a polynomial chart to the chart itself; it is
the identity on affine spaces. -/
private def restrictHom (Q : PolynomialChart Λ X structureMap) (R : X.Opens)
    (h : R ≤ Q.openPart) : Hom (restrict Q R h) Q where
  open_le := h
  affine := 𝟙 Q.affineSpace
  map_comm := by simp [restrict]
  base_comm := rfl

/-- A morphism lies over any morphism of the base when the base has at most one such morphism. -/
private theorem isHomLift_of_subsingleton {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮] (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} (φ : a ⟶ b) (f : p.obj a ⟶ p.obj b) [Subsingleton (p.obj a ⟶ p.obj b)] :
    p.IsHomLift f φ := by
  rw [Subsingleton.elim f (p.map φ)]
  exact .map φ

/-- The restriction morphism of a polynomial chart is strongly cartesian over the inclusion of
open subschemes it lies above. -/
private theorem restrict_isStronglyCartesian (Q : PolynomialChart Λ X structureMap)
    {R : X.Opens} (f : R ⟶ Q.openPart) :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsStronglyCartesian f
      (restrictHom Q R f.down.down) := by
  let P := restrict Q R f.down.down
  let φ := restrictHom Q R f.down.down
  let p := openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)
  let : p.IsHomLift f φ := isHomLift_of_subsingleton p φ f
  refine { universal_property' := ?_ }
  intro T g φ' _hφ
  let ψ : Hom T P :=
    { open_le := g.down.down
      affine := φ'.affine
      map_comm := by
        change T.toAffine ≫ φ'.affine =
          X.homOfLE g.down.down ≫ (X.homOfLE f.down.down ≫ Q.toAffine)
        rw [← Category.assoc, X.homOfLE_homOfLE]
        exact φ'.map_comm
      base_comm := φ'.base_comm }
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_of_subsingleton p ψ g
  · exact Hom.ext (Category.comp_id φ'.affine)
  · intro χ hχ
    have hc := congrArg Hom.affine hχ.2
    change χ.affine ≫ 𝟙 Q.affineSpace = φ'.affine at hc
    exact Hom.ext ((Category.comp_id χ.affine).symm.trans hc)

end

/-- **Stacks 08V9.** Polynomial charts over `X` form a category fibred over the Zariski
category of `X`. -/
@[stacks 08V9]
instance openFunctor_isFibered (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ)) :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsFibered :=
  .of_exists_isStronglyCartesian fun Q R f =>
    ⟨restrict Q R f.down.down, restrictHom Q R f.down.down, restrict_isStronglyCartesian Q f⟩

end AlgebraicGeometry.PolynomialChart

end
