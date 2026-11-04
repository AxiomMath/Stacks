module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The trace map of a right adjoint of derived pushforward

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `a` be a right
adjoint of derived pushforward `Rf_* : D(O_C) ⥤ D(O_D)`.  For `L` in `D(O_C)` and `K` in
`D(O_D)` there is a canonical map

`Rf_*RHom_{O_C}(L, a(K)) ⟶ RHom_{O_D}(Rf_*L, K)`,

Equation 86.3.2.1 of [Stacks, Tag 0E57].  It is the composition

`Rf_*RHom_{O_C}(L, a(K)) ⟶ RHom_{O_D}(Rf_*L, Rf_*a(K)) ⟶ RHom_{O_D}(Rf_*L, K)`,

whose first arrow is the projection formula for derived internal Hom of [Stacks, Tag 0B6D] and
whose second is `RHom_{O_D}(Rf_*L, −)` applied to the counit `Rf_*a(K) ⟶ K` of the adjunction
`Rf_* ⊣ a`.

## Main definitions

All in the namespace `Stacks.Cohomology.PushforwardTraceOnRingedTopoi`.

* `pushforwardTrace` — **Equation 86.3.2.1**, that composition.

## Main results

* `pushforwardTrace_eq` — the trace map *is* that composition, so a consumer never unfolds the
  definition.
* `pushforwardTrace_naturality_source` and `pushforwardTrace_naturality_target` — the trace map
  is contravariant in `L` and covariant in `K`.

## Implementation notes

*The right adjoint is a hypothesis.*  The source obtains `a` from [Stacks, Tag 0E55], which
asserts that `Rf_*` has a right adjoint for a morphism of quasi-compact and quasi-separated
algebraic spaces; that is an existence statement and it is not part of this development.  The
formula for the trace map does not depend on how `a` arises — only on an adjunction
`Rf_* ⊣ a`, whose counit is the second arrow — so `a` and the adjunction are carried as
hypotheses and nothing is chosen here.  Both naturality clauses are proved from the naturality
of [Stacks, Tag 0B6D] and the naturality of that counit.

*The source's setting is the special case.*  [Stacks, Tag 0E57] states the map for `X` and `Y`
quasi-compact and quasi-separated algebraic spaces over a scheme, with `a` the right adjoint of
`Rf_* : D_QCoh(O_X) ⥤ D_QCoh(O_Y)`.  Taking `(Sh(C), O_C)` and `(Sh(D), O_D)` to be the small
étale ringed topoi of `X` and of `Y`, and `a` to be that right adjoint, specialises the
statement below to the source's.  Nothing of the construction uses quasi-compactness,
quasi-separatedness or quasi-coherence: those hypotheses of the source are what produce `a`, and
they enter only through the adjunction.

*The tensor–internal-Hom adjunction.*  The internal Hom bifunctors `HX`, `HY` and the
tensor–internal-Hom adjunctions `DX`, `DY` on `D(O_C)` and `D(O_D)` are the data of
[Stacks, Tag 0B6D] in this development; see the implementation notes of
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi` for why the adjunction is carried
and the relative cup product of [Stacks, Tag 0B6C] is not.

## References

* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.PushforwardTraceOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (HX : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (HY : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.O) HX)
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.O) HY)
  {a : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (adj : derivedPushforward f ⊣ a)

/-- **Equation 86.3.2.1 of [Stacks, Tag 0E57].**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, a right adjoint `a` of `Rf_*`, and objects `L` of `D(O_C)`
and `K` of `D(O_D)`, the canonical map

`Rf_*RHom_{O_C}(L, a(K)) ⟶ RHom_{O_D}(Rf_*L, K)`.

It is the projection formula for derived internal Hom of [Stacks, Tag 0B6D] at `L` and `a(K)`,
followed by `RHom_{O_D}(Rf_*L, −)` applied to the counit `Rf_*a(K) ⟶ K` of `Rf_* ⊣ a`. -/
@[stacks 0E57]
def pushforwardTrace
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPushforward f).obj ((HX.obj (op L)).obj (a.obj K)) ⟶
      (HY.obj (op ((derivedPushforward f).obj L))).obj K :=
  projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
    DY.toTensorHomBijection L (a.obj K) ≫
    (HY.obj (op ((derivedPushforward f).obj L))).map (adj.counit.app K)

/-- **The trace map is that composition.**  Equation 86.3.2.1 is the projection formula for
derived internal Hom of [Stacks, Tag 0B6D] followed by the derived internal Hom out of `Rf_*L`
of the counit `Rf_*a(K) ⟶ K`, and this records it as an equation, so a consumer never unfolds
the definition. -/
@[stacks 0E57 "the defining composition"]
theorem pushforwardTrace_eq
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    pushforwardTrace f hmos HX HY DX DY adj L K =
      projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
        DY.toTensorHomBijection L (a.obj K) ≫
        (HY.obj (op ((derivedPushforward f).obj L))).map (adj.counit.app K) :=
  rfl

/-- **The trace map is contravariant in `L`.** -/
@[stacks 0E57 "naturality in the first variable"]
theorem pushforwardTrace_naturality_source
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L' ⟶ L)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPushforward f).map ((HX.map g.op).app (a.obj K)) ≫
        pushforwardTrace f hmos HX HY DX DY adj L' K =
      pushforwardTrace f hmos HX HY DX DY adj L K ≫
        (HY.map ((derivedPushforward f).map g).op).app K := by
  dsimp only [pushforwardTrace]
  rw [← Category.assoc, projectionFormulaInternalHomMap_naturality_source, Category.assoc,
    ← (HY.map ((derivedPushforward f).map g).op).naturality, Category.assoc]

/-- **The trace map is covariant in `K`.** -/
@[stacks 0E57 "naturality in the second variable"]
theorem pushforwardTrace_naturality_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (φ : K ⟶ K') :
    (derivedPushforward f).map ((HX.obj (op L)).map (a.map φ)) ≫
        pushforwardTrace f hmos HX HY DX DY adj L K' =
      pushforwardTrace f hmos HX HY DX DY adj L K ≫
        (HY.obj (op ((derivedPushforward f).obj L))).map φ := by
  have hcounit : (derivedPushforward f).map (a.map φ) ≫ adj.counit.app K' =
      adj.counit.app K ≫ φ := by
    simp
  dsimp only [pushforwardTrace]
  rw [← Category.assoc, projectionFormulaInternalHomMap_naturality_target, Category.assoc,
    ← Functor.map_comp, hcounit, Functor.map_comp, Category.assoc]

end Stacks.Cohomology.PushforwardTraceOnRingedTopoi

end
