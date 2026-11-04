module

public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.SmallIndex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# A finite algebra sheaf as a colimit of finitely presented ones, indexed in `Type u`

Let `X` be a quasi-compact and quasi-separated scheme and `A` a finite quasi-coherent sheaf of
commutative `𝒪_X`-algebras.  [Stacks, Tag 086N] presents `A` as a directed colimit of finite and
finitely presented quasi-coherent algebras, and
`Stacks.FiniteAlgebraLimitPresentation.exists_isColimit_finite_finitePresentation` proves it with
an index in `Type (u + 1)`: the index is the one of the limit presentation of [Stacks, Tag 09YY],
whose `Stacks.FiniteAlgebraLimitPresentation.FiniteLimitPresentation.indexType` is declared one
universe above the schemes in faithfulness to that tag.

That extra universe is an artefact and this file removes it.  The presentation actually built by
`Stacks.FiniteAlgebraLimitPresentation.finiteLimitPresentationOfIsFinite` is a `ULift` of a
cofinal tail of the index of [Stacks, Tag 09ZQ], which already lies in `Type u`; so its index is
`u`-small, and `Stacks.SmallIndex.exists_small_index_finite_finitePresentation` reindexes the
resulting colimit by a nonempty directed preorder in `Type u`.

## Main results

* `Stacks.FiniteAlgebraLimitPresentation.small_indexType_finiteLimitPresentationOfIsFinite`: the
  index of the limit presentation of [Stacks, Tag 09YY] built by
  `finiteLimitPresentationOfIsFinite` is `u`-small.
* `Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation`:
  **[Stacks, Tag 086N] with the index in `Type u`.**

## Implementation notes

The smallness instance holds by unification: the index is literally a `ULift` of a type in
`Type u`, so `small_ulift` applies with the `ULift`ed type left to the elaborator.  No property of
the limit presentation is used, only the shape of the type it indexes by.

The colimit itself is not reindexed by hand.  The proof is the proof of
`exists_isColimit_finite_finitePresentation_of_finiteLimitPresentation` with
`finiteLimitPresentationOfIsFinite` supplied for [Stacks, Tag 09YY] and the final packaging
replaced by `Stacks.SmallIndex.exists_small_index_finite_finitePresentation`, which is where the
smallness is consumed; it cannot be obtained from the statement of
`exists_isColimit_finite_finitePresentation`, whose index is existentially quantified and
therefore carries no smallness.

No `@[stacks 086N]` attribute is attached: the tag is carried by
`exists_isColimit_finite_finitePresentation`, and the statement below is a reindexing of it which
additionally forgets the surjectivity of the transition maps.

## References

* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 09YY](https://stacks.math.columbia.edu/tag/09YY)
* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec

universe u

namespace Stacks.FiniteAlgebraLimitPresentation

/-- The index of the limit presentation of [Stacks, Tag 09YY] produced by
`Stacks.FiniteAlgebraLimitPresentation.finiteLimitPresentationOfIsFinite` is `u`-small: it is the
`ULift` to `Type (u + 1)` of a cofinal tail of the index supplied by [Stacks, Tag 09ZQ], which
lies in `Type u`. -/
instance small_indexType_finiteLimitPresentationOfIsFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [CompactSpace S] [QuasiSeparatedSpace S] :
    Small.{u} (finiteLimitPresentationOfIsFinite f).indexType :=
  small_ulift _

/-- **[Stacks, Tag 086N] with the index in `Type u`.**  On a quasi-compact and quasi-separated
scheme, a finite quasi-coherent algebra is the colimit of a directed system, indexed by a nonempty
directed preorder in the universe of the scheme, of quasi-coherent algebras which are finite and
of finite presentation.

The system is the one of `exists_isColimit_finite_finitePresentation`, transported along
`Stacks.SmallIndex.exists_small_index_finite_finitePresentation`; the surjectivity of the
transition maps recorded there is forgotten. -/
theorem exists_small_isColimit_finite_finitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (A : AlgebraSheaf X) (hAqc : A.IsQuasicoherent) (hAfin : A.IsFinite) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation := by
  let E := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.{u}
  let e := E.equivalence X
  let a : QuasicoherentAlgebra X := ⟨A, hAqc⟩
  let Y := (e.inverse.obj a).unop
  have : IsAffineHom Y.obj.hom := Y.property
  let eA : A ≅ pushforwardAlgebra Y.obj.hom :=
    (IsQuasicoherentAlgebra X).ι.mapIso (e.counitIso.app a).symm ≪≫
      E.pushforwardIso X Y
  have hYfin : IsFinite Y.obj.hom :=
    (pushforwardAlgebra_isFinite_iff Y.obj.hom).mp (isFinite_of_iso eA.symm hAfin)
  let P := finiteLimitPresentationOfIsFinite Y.obj.hom
  let _ : Preorder P.indexType := P.indexPreorder
  have : Nonempty P.indexType := P.indexNonempty
  have : IsDirected P.indexType (· ≤ ·) := P.indexDirected
  have : Small.{u} P.indexType := small_indexType_finiteLimitPresentationOfIsFinite Y.obj.hom
  have : IsConnected P.indexTypeᵒᵖ := IsCofiltered.isConnected _
  let D : P.indexTypeᵒᵖ ⥤ AffineOver X :=
    (IsAffineHomOver X).lift
      (Over.lift P.diagram P.structureMap)
      (fun i => (P.stageFinite i).toIsAffineHom)
  let p (i : P.indexTypeᵒᵖ) : Y ⟶ D.obj i :=
    ⟨Over.homMk (P.limitCone.app i) (P.compatible i).symm⟩
  have hp {i j : P.indexTypeᵒᵖ} (g : i ⟶ j) : p i ≫ D.map g = p j := by
    ext
    show P.limitCone.app i ≫ P.diagram.map g = P.limitCone.app j
    simpa using (P.limitCone.naturality g).symm
  let c : Cone D := Cone.mk Y
    { app := p
      naturality := fun _ _ g => by simpa using (hp g).symm }
  have hcOver : IsLimit ((IsAffineHomOver X).ι.mapCone c) :=
    Over.isLimitLiftCone P.diagram P.structureMap (Cone.mk Y.obj.left P.limitCone) Y.obj.hom
      (fun i => (P.compatible i).symm) P.isLimit
  let i : (IsQuasicoherentAlgebra X).ι.obj ((E.equivalence X).functor.obj (.op c.pt)) ⟶ A :=
    (IsQuasicoherentAlgebra X).ι.map (e.counitIso.app a).hom
  have : IsIso i := inferInstanceAs
    (IsIso ((IsQuasicoherentAlgebra X).ι.map (e.counitIso.app a).hom))
  refine Stacks.SmallIndex.exists_small_index_finite_finitePresentation A
    (G := transportedDiagram E X D) (transportedCocone E X c i).ι
    (isColimitTransportedCocone E X c hcOver i) fun k => ?_
  have : IsAffineHom (D.obj (.op k)).obj.hom := (D.obj (.op k)).property
  exact ⟨((E.equivalence X).functor.obj (.op (D.obj (.op k)))).property,
    isFinite_of_iso (E.pushforwardIso X (D.obj (.op k)))
      ((pushforwardAlgebra_isFinite_iff (D.obj (.op k)).obj.hom).mpr (P.stageFinite (.op k))),
    isFinitePresentation_of_iso (E.pushforwardIso X (D.obj (.op k)))
      (pushforwardAlgebra_isFinitePresentation (D.obj (.op k)).obj.hom
        (P.stageFinitePresentation (.op k)))⟩

end Stacks.FiniteAlgebraLimitPresentation

end
