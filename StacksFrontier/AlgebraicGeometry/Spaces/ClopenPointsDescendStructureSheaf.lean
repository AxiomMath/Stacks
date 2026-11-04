module

public import StacksFrontier.AlgebraicGeometry.Scheme.ClopenIdempotent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ClopenGlobalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Clopen sets of points, idempotent global functions, and `f_*𝒪_X = 𝒪_Y`

Two facts about an algebraic space `F` over a scheme `S` and its point space `|F|`.

First, every open and closed subset `A` of `|F|` is the support of an idempotent global regular
function of `F` (the base's `AlgebraicGeometry.Space.exists_isIdempotentElem_sectionSupport_eq`,
in `StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso`): on each étale scheme
chart it is the idempotent whose nonvanishing locus is the (clopen) part of the chart lying over
`A`.

Second, let `f : X ⟶ Y` be a morphism of algebraic spaces whose structure map
`𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, and `V` an étale scheme chart of `Y`.  Then every open and
closed subset of `|X ×_Y V|` is the preimage of a subset of `V`
(`AlgebraicGeometry.Space.exists_eq_preimage_of_isClopen_of_isIso_fSharp`): its idempotent is
a global function on `X ×_Y V`, hence a section of `f_*𝒪_X` over `V`
(`AlgebraicGeometry.Space.surjective_directImageSectionsToGlobalFunctions`), hence the
pullback of a function `r` on `V`, and the support of a pulled back function is the preimage of
the nonvanishing locus of `r`.  This is the form in which the connectedness clause of
Stacks 0A1C uses `f'_*𝒪_X = 𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.exists_eq_preimage_of_isClopen_of_isIso_fSharp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clopen sets of points descend along `f` when `f_*𝒪_X = 𝒪_Y` -/

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- **Clopen sets of points descend when `f_*𝒪_X = 𝒪_Y`.**  Let `f : X ⟶ Y` be a morphism of
algebraic spaces whose structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, and let `V` be an étale
scheme chart of `Y`.  Every open and closed set of points of `X ×_Y V` is the preimage, under the
projection to `V`, of a set of points of the scheme `V`. -/
theorem exists_eq_preimage_of_isClopen_of_isIso_fSharp (f : X ⟶ Y)
    (hf : IsIso (smallEtaleRingedToposHom B S hS f).fSharp) (V : SmallEtale B S hS Y.1)
    (A : Set (points B S hS (chartBaseChangeSpace B S hS f V).obj)) (hA : IsClopen A) :
    ∃ D : Set ((BigFppfOver.toScheme B S hS).obj V.obj.left),
      ∀ x, x ∈ A ↔ pointsToScheme B S hS V.obj.left
        (pointsMap B S hS _ (chartBaseChangeProjection B S hS f V).hom x) ∈ D := by
  obtain ⟨e, -, hsupp⟩ := exists_isIdempotentElem_sectionSupport_eq B S hS _
    (chartBaseChangeSpace B S hS f V).property A hA
  obtain ⟨s, hs⟩ := surjective_directImageSectionsToGlobalFunctions B S hS f V e
  have hiso : IsIso (((sheafToPresheaf _ _).map
      (smallEtaleRingedToposHom B S hS f).fSharp).app (op V)) := inferInstance
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso
    (((sheafToPresheaf _ _).map (smallEtaleRingedToposHom B S hS f).fSharp).app (op V))).2 s
  refine ⟨((BigFppfOver.toScheme B S hS).obj V.obj.left).basicOpen r, fun x => ?_⟩
  obtain ⟨c, p, rfl⟩ := exists_chart_point B S hS _ (chartBaseChangeSpace B S hS f V).property x
  rw [← hsupp, mem_sectionSupport_iff]
  have hval : e.val (op c) = ((BigFppfOver.toScheme B S hS).map
      (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom
        r := by
    rw [← hs, ← hr]
    exact directImageSectionsToGlobalFunctions_algebraMap B S hS f V c r
  rw [hval]
  refine (Iff.of_eq (congrArg
    (fun O : ((BigFppfOver.toScheme B S hS).obj c.obj.left).Opens =>
      pointsToScheme B S hS c.obj.left p ∈ O)
    (Scheme.preimage_basicOpen_top _ r).symm)).trans ?_
  have heq : (BigFppfOver.toScheme B S hS).map
      (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c)
      (pointsToScheme B S hS c.obj.left p) =
        pointsToScheme B S hS V.obj.left (pointsMap B S hS _
          (chartBaseChangeProjection B S hS f V).hom (pointsMap B S hS _ c.obj.hom p)) := by
    refine (pointsToScheme_pointsMap_yoneda B S hS _ p).symm.trans
      (congrArg (pointsToScheme B S hS V.obj.left) ?_)
    exact (congrArg (fun m => pointsMap B S hS _ m p)
      (yoneda_map_smallEtaleChartMapToBase B S hS _ c)).trans
      (congrFun (pointsMap_comp B S hS _ _ _) p)
  exact Iff.of_eq (congrArg
    (fun y => y ∈ ((BigFppfOver.toScheme B S hS).obj V.obj.left).basicOpen r) heq)

end AlgebraicGeometry.Space

end
