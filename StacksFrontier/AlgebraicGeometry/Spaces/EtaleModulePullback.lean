module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# Pullback of modules along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Postcomposition with `f` carries an étale chart of `X` to an étale chart of `Y`
with the *same* underlying scheme, so the structure sheaf of the small étale site of `Y`
restricts along `AlgebraicGeometry.Space.smallEtalePostcomp` to the structure sheaf of the small
étale site of `X`, on the nose.  Pullback of modules along `f` is therefore plain restriction
along postcomposition, with no change of scalars.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePullback` is the pullback of `𝒪_Y`-modules to
  `𝒪_X`-modules along an étale `f : X ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`: its sections over a chart of `X`
  are the sections of the original module over the composite chart of `Y`.

## Implementation notes

The functor is `SheafOfModules.pushforward` for the continuous functor
`AlgebraicGeometry.Space.smallEtalePostcomp` — pushforward of sheaves of modules along a
continuous functor is restriction of sections, hence *inverse* image in geometric direction —
taken at the structure map `𝟙 (RingedSite.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2))`.
That identity typechecks exactly because restricting the structure sheaf of `Y` along
postcomposition gives the structure sheaf of `X` definitionally, which is in turn because
`AlgebraicGeometry.Space.smallEtalePostcomp_comp_toOver` is `rfl` and both structure sheaves are
global regular functions on the underlying scheme.  So no change of scalars occurs, the module
universe `m` stays free, and the sections are given by a `rfl` lemma.

The continuity instance is restated for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold, exactly
as `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` restates sheafification;
without it `AlgebraicGeometry.Space.smallEtalePostcomp_isContinuous` does not fire at the goal
produced by `SheafOfModules.pushforward`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Postcomposition along an étale morphism of algebraic spaces is continuous for the
topologies of the small étale ringed sites.

The content is `AlgebraicGeometry.Space.smallEtalePostcomp_isContinuous`; this restates it for
the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does
not unfold. -/
instance smallEtaleRingedSite_isContinuous_smallEtalePostcomp
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtalePostcomp B S hS f hf).IsContinuous
      (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallEtaleRingedSite B S hS Y.1 Y.2).J := by
  change (smallEtalePostcomp B S hS f hf).IsContinuous
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
  infer_instance

/-- Pullback of modules along an étale morphism `f : X ⟶ Y` of algebraic spaces: restriction of
sheaves of modules along postcomposition of étale charts with `f`.

Since postcomposition leaves the underlying scheme of a chart unchanged, so do its ring of
sections and the modules over it; the module universe is therefore unconstrained. -/
noncomputable def etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Modules.{u, m} B S hS Y.1 Y.2 ⥤ Modules.{u, m} B S hS X.1 X.2 :=
  SheafOfModules.pushforward (F := smallEtalePostcomp B S hS f hf)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- The sections of an étale pullback over a chart of `X` are the sections of the original
module over the composite chart of `Y`, as a module over the same ring of regular functions. -/
theorem etaleModulePullback_obj_val_obj (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, m} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1) :
    ((etaleModulePullback B S hS f hf).obj M).val.obj (Opposite.op U) =
      M.val.obj (Opposite.op ((smallEtalePostcomp B S hS f hf).obj U)) := rfl

/-- A morphism of the étale pullbacks of two `𝒪_Y`-modules, read on sections over a chart `U` of
`X` as a map of the sections of the two modules over the composite chart of `Y`.

This is the morphism-level companion of
`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`: the result type is ascribed, so that
the identification of the structure ring of `U` with the structure ring of the composite chart is
performed here once and for all rather than at every use. -/
noncomputable def etaleModulePullbackHomApp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M N : Modules.{u, m} B S hS Y.1 Y.2}
    (ψ : (etaleModulePullback B S hS f hf).obj M ⟶ (etaleModulePullback B S hS f hf).obj N)
    (U : SmallEtale B S hS X.1) :
    M.val.obj (Opposite.op ((smallEtalePostcomp B S hS f hf).obj U)) ⟶
      N.val.obj (Opposite.op ((smallEtalePostcomp B S hS f hf).obj U)) :=
  ψ.val.app (Opposite.op U)

/-- The reading of a morphism of étale pullbacks over a chart of `X` is that morphism on
sections, the sections of an étale pullback over a chart being the sections of the original
module over the composite chart. -/
theorem etaleModulePullbackHomApp_apply (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M N : Modules.{u, m} B S hS Y.1 Y.2}
    (ψ : (etaleModulePullback B S hS f hf).obj M ⟶ (etaleModulePullback B S hS f hf).obj N)
    (U : SmallEtale B S hS X.1)
    (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS f hf).obj U))) :
    etaleModulePullbackHomApp B S hS f hf ψ U t = ψ.val.app (Opposite.op U) t := rfl

/-- The reading of a morphism of étale pullbacks over a chart of `X` *is* that morphism on
sections over the chart, as a morphism of the groups of sections. -/
theorem etaleModulePullbackHomApp_eq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M N : Modules.{u, m} B S hS Y.1 Y.2}
    (ψ : (etaleModulePullback B S hS f hf).obj M ⟶ (etaleModulePullback B S hS f hf).obj N)
    (U : SmallEtale B S hS X.1) :
    etaleModulePullbackHomApp B S hS f hf ψ U = ψ.val.app (Opposite.op U) := rfl

end AlgebraicGeometry.Space

end
