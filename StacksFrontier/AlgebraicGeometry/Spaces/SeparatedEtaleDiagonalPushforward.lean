module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePushforwardSplitCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.UnitSplitEpiTransport

/-!
# The direct image of modules along the diagonal of a separated étale morphism, on charts

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, and let `Δ : X ⟶ X ×_Y X` be its relative diagonal. Then `Δ` is representable,
and the direct image of modules along `Δ` is computed on charts:

`(Δ_*ℱ)(V) = ℱ(V ×_{X ×_Y X} X)`,

and the unit `ℳ ⟶ Δ_*Δ^*ℳ` is, over an étale chart `V` of `X ×_Y X`, restriction of sections along
the cartesian projection `V ×_{X ×_Y X} X ⟶ V`. Consequently, with `p : X ×_Y X ⟶ X` the first
projection, the counit `f^*f_*ℱ ⟶ ℱ` is a split epimorphism as soon as the unit of the
chart-level adjunction `Δ^* ⊣ (- ×_{X ×_Y X} X)` is a split epimorphism at `p^*ℱ`.

## Main definitions

* `AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction`: the adjunction
  `Δ^* ⊣ (- ×_{X ×_Y X} X)` of charts and modules at the diagonal of a separated étale morphism.
* `AlgebraicGeometry.Space.diagonalSmallBaseChangeModulePushforwardIso`: the identification of its
  right adjoint with the direct image `Δ_*`.
* `AlgebraicGeometry.Space.splitEpiDiagonalUnitOfSplitEpiChartUnit` and
  `AlgebraicGeometry.Space.counitSplitEpiOfSplitEpiChartUnit`: the transport of a splitting.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_selfFibreDiagonal`: the relative diagonal of a
  separated morphism of algebraic spaces is representable.
* `AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction_unit_app_val_app`: the unit of that
  adjunction is restriction of sections along the cartesian projection of charts.
* `AlgebraicGeometry.Space.splitEpiDiagonalUnitOfSplitEpiChartUnit`: a splitting of the chart-level
  unit splits the unit `ℳ ⟶ Δ_*Δ^*ℳ`.
* `AlgebraicGeometry.Space.counitSplitEpiOfSplitEpiChartUnit`: a splitting of the chart-level unit
  at `p^*ℱ` splits the counit `f^*f_*ℱ ⟶ ℱ`.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Representability of the diagonal -/

/-- The relative diagonal of a separated morphism of algebraic spaces is representable. -/
theorem relativelyRepresentable_selfFibreDiagonal (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) :
    yoneda.relativelyRepresentable (selfFibreDiagonal B S hS f).hom :=
  hsep.rep

/-! ### The chart-level adjunction at the diagonal -/

/-- Restriction of modules along the diagonal of a separated étale morphism is left adjoint to
restriction of sections along base change of charts. -/
noncomputable def diagonalSmallBaseChangeAdjunction (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) :
    etaleModulePullback.{u, u} B S hS (selfFibreDiagonal B S hS f)
        (isEtale_selfFibreDiagonal B S hS f het) ⊣
      smallBaseChangeModulePushforward.{u, u} B S hS (selfFibreDiagonal B S hS f)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) :=
  etaleModulePullbackSmallBaseChangeAdjunction B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)

/-- The direct image of modules along the diagonal of a separated étale morphism is restriction of
sections along base change of charts. -/
noncomputable def diagonalSmallBaseChangeModulePushforwardIso (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    smallBaseChangeModulePushforward.{u, u} B S hS (selfFibreDiagonal B S hS f)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) ≅
      modulePushforward B S hS (selfFibreDiagonal B S hS f) :=
  smallBaseChangeModulePushforwardIso B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)

/-- The sections of the direct image of a module along the diagonal over an étale chart `V` of
`X ×_Y X` are its sections over the base-changed chart `V ×_{X ×_Y X} X`. -/
theorem diagonalSmallBaseChangeModulePushforward_obj_val_obj (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (((smallBaseChangeModulePushforward.{u, u} B S hS (selfFibreDiagonal B S hS f)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj M).val.obj
          (Opposite.op V) : Type u) =
      (M.val.obj (Opposite.op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V)) : Type u) :=
  rfl

/-- The unit of the chart-level adjunction at the diagonal is restriction of sections along the
cartesian projection `V ×_{X ×_Y X} X ⟶ V` of charts. -/
theorem diagonalSmallBaseChangeAdjunction_unit_app_val_app (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (N : Modules.{u, u} B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2)
    (V : (SmallEtale B S hS (selfFibreSquare B S hS f).1)ᵒᵖ)
    (x : ((N.val.obj V : ModuleCat _) : Type u)) :
    ((diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app N).val.app V x =
      N.val.map ((smallEtalePostcompBaseChangeAdjunction B S hS
        (selfFibreDiagonal B S hS f) (isEtale_selfFibreDiagonal B S hS f het)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).counit.app V.unop).op x :=
  etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app B S hS
    (selfFibreDiagonal B S hS f) (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) N V x

/-- The underlying morphism of the big fppf site of the counit of the chart-level adjunction at the
diagonal is the cartesian projection `V ×_{X ×_Y X} X ⟶ V`. -/
theorem diagonalSmallEtalePostcompBaseChangeAdjunction_counit_left (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    ((smallEtalePostcompBaseChangeAdjunction B S hS (selfFibreDiagonal B S hS f)
        (isEtale_selfFibreDiagonal B S hS f het)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).counit.app V).hom.left =
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep).snd V.1.hom :=
  smallEtalePostcompBaseChangeAdjunction_counit_left B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) V

/-! ### Transport of the splitting -/

/-- A splitting of the chart-level unit at the diagonal splits the unit `N ⟶ Δ_*Δ^*N` of the
adjunction between pullback and direct image of modules. -/
noncomputable def splitEpiDiagonalUnitOfSplitEpiChartUnit (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (N : Modules.{u, u} B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2)
    (hsplit : SplitEpi ((diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app N)) :
    SplitEpi ((modulePullbackAdjunction B S hS (selfFibreDiagonal B S hS f)).unit.app N) :=
  Stacks.Adjunction.splitEpiUnitOfSplitEpiUnitOfIsoLeft
    (modulePullbackAdjunction B S hS (selfFibreDiagonal B S hS f))
    (diagonalSmallBaseChangeAdjunction B S hS f het hsep)
    (modulePullbackIsoEtaleModulePullback B S hS (selfFibreDiagonal B S hS f)
      (isEtale_selfFibreDiagonal B S hS f het)) N hsplit

/-- Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces and `ℱ` an `𝒪_X`-module. If
the unit of the chart-level adjunction `Δ^* ⊣ (- ×_{X ×_Y X} X)` is a split epimorphism at `p^*ℱ`,
with `p : X ×_Y X ⟶ X` the first projection, then the counit `f^*f_*ℱ ⟶ ℱ` is a split
epimorphism. -/
noncomputable def counitSplitEpiOfSplitEpiChartUnit (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hsplit : SplitEpi ((diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app
      ((etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
        (isEtale_selfFibreFst B S hS f het)).obj F))) :
    SplitEpi ((modulePullbackAdjunction B S hS f).counit.app F) :=
  counitSplitEpiOfSplitEpiDiagonalUnit B S hS f het F
    (splitEpiDiagonalUnitOfSplitEpiChartUnit B S hS f het hsep _ hsplit)

end AlgebraicGeometry.Space

end
