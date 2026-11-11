module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor

/-!
# The germ decomposition of a finite-support stalk, functorially in the sheaf

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `ȳ` be a geometric
point of `Y`. Stacks 0F6P states that, functorially in `F` in `Ab(X_étale)`,
`(f_{p!}F)_ȳ = ⊕_{f(x̄) = ȳ} F_x̄`. The objectwise isomorphism is
`AlgebraicGeometry.SmallEtale.finiteSupportStalkIso`; here it is assembled into an isomorphism
of functors from abelian sheaves on the small étale site of `X` to abelian groups.

## Main definitions

* `AlgebraicGeometry.SmallEtale.finiteSupportStalkFunctorIso` — the isomorphism of functors
  `(F ↦ (f_{p!}F)_ȳ) ≅ (F ↦ ⊕_{f(x̄) = ȳ} F_x̄)`.

## Implementation notes

The source functor is the finite-support direct image `f_{p!}` followed by the stalk functor
`AlgebraicGeometry.etaleStalkPresheafFunctor` at `ȳ`; the target functor is
`AlgebraicGeometry.SmallEtale.fiberStalksFunctor`, the external direct sum of the stalks with
`AlgebraicGeometry.SmallEtale.fiberStalksMap` on morphisms. The naturality square is
`AlgebraicGeometry.SmallEtale.finiteSupportStalkToFiberStalks_natural`.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))

/-- **Stacks 0F6P.** For a locally quasi-finite morphism `f : X ⟶ Y` and a geometric point `ȳ`
of `Y`, functorially in the abelian sheaf `F` on the small étale site of `X`, the stalk at `ȳ` of
the finite-support direct image `f_{p!}F` is the direct sum of the stalks of `F` over the
geometric points of `X` lying over `ȳ`: `(f_{p!}F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. The component at `F`
is `finiteSupportStalkIso`. -/
@[stacks 0F6P "the germ decomposition as an isomorphism of functors on `Ab(X_étale)`"]
public def finiteSupportStalkFunctorIso :
    (finiteSupportPushforward B f hsmall).1 ⋙
        etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max u v} ≅
      fiberStalksFunctor.{u, v} B f s :=
  NatIso.ofComponents (fun F => finiteSupportStalkIso B f s F hsmall)
    (fun φ => finiteSupportStalkToFiberStalks_natural B f s hsmall φ)

/-- The component of `finiteSupportStalkFunctorIso` at a sheaf `F` is the germ decomposition
isomorphism `finiteSupportStalkIso` of `F`. -/
@[simp]
public lemma finiteSupportStalkFunctorIso_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v}) :
    (finiteSupportStalkFunctorIso B f s hsmall).app F = finiteSupportStalkIso B f s F hsmall :=
  rfl

end AlgebraicGeometry.SmallEtale
