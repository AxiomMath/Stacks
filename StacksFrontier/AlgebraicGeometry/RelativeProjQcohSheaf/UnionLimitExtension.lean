module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRepresentable

/-!
# Naturality of the comparison between the inverse limit and the union in display 01NX

The display 01NX defines `F : Sch^{opp} ⟶ Sets` in two cases: for a quasi-compact test scheme `T`
the value is the union `F(T) = ⋃_{d ≥ 1} F_d(T)`, which is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.functor`, and for a general `T` it is the inverse
limit of those unions over the quasi-compact opens of `T`, which is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limFunctor`. The bijection
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limEquiv` between them at a quasi-compact test
scheme commutes with the maps of the two functors on morphisms.

## Main results

* `AlgebraicGeometry.Scheme.QcExtension.equivObj_naturality`: for an arbitrary
  `Φ : Sch^{opp} ⟶ Sets`, the bijection `Φ^{qc}(T) ≃ Φ(T)` at a quasi-compact `T` is natural in
  `T` along the morphisms between quasi-compact schemes.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limEquiv_naturality`: for `g : T' ⟶ T` a
  morphism of quasi-compact test schemes, the bijection `F.limEquiv` identifies the map
  `F(T) → F(T')` of the inverse-limit functor with the pullback of a quadruple along `g`.

## References

* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace

universe u v

namespace AlgebraicGeometry.Scheme

variable {T T' : Scheme.{u}} (Φ : Scheme.{u}ᵒᵖ ⥤ Type v)

/-- For `g : T' ⟶ T` a morphism of quasi-compact schemes, the bijection
`QcExtension.equivObj Φ` between the quasi-compact extension of `Φ` and `Φ` is natural along `g`:
reindexing a compatible family along `g` and taking its value at `𝟙 T'` gives the image under
`Φ.map g.op` of its value at `𝟙 T`. -/
theorem QcExtension.equivObj_naturality (g : T' ⟶ T)
    (hT : CompactSpace T) (hT' : CompactSpace T') (s : QcExtension Φ T) :
    QcExtension.equivObj Φ T' hT' (QcExtension.pullback Φ g s)
      = Φ.map g.op (QcExtension.equivObj Φ T hT s) := by
  show (QcExtension.pullback Φ g s).val T' hT' (𝟙 T') = Φ.map g.op (s.val T hT (𝟙 T))
  rw [s.compat T T' hT hT' g (𝟙 T), QcExtension.pullback_val, Category.id_comp,
    Category.comp_id]

end AlgebraicGeometry.Scheme

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S T T' : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-- For `g : T' ⟶ T` a morphism of quasi-compact test schemes, the bijection `F.limEquiv` between
the inverse limit over the quasi-compact opens and the union `F(T) = ⋃_{d ≥ 1} F_d(T)` carries the
map of `F.limFunctor` along `g` to the pullback of a quadruple along `g`. -/
theorem F.limEquiv_naturality (g : T' ⟶ T) (hT : CompactSpace T) (hT' : CompactSpace T')
    (s : Scheme.QcExtension (F.functor A) T) :
    F.limEquiv A T' hT' ((F.limFunctor A).map g.op s)
      = F.pullback g (F.limEquiv A T hT s) :=
  Scheme.QcExtension.equivObj_naturality (F.functor A) g hT hT' s

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
