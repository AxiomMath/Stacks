module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartDiagramsOfQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The sections of a quasi-coherent module over an affine chart, as a cokernel

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M` be a
quasi-coherent `𝒪_X`-module and let `W` be an étale scheme chart of `X` whose underlying scheme
is affine.  The small étale site of the algebraic space represented by `W` has a terminal
object, the identity chart `AlgebraicGeometry.Space.idEtaleChart`, and the sections of the
restriction of `M` to that chart space over that terminal object are, definitionally, the
sections `M(W)`.  That chart space is affine as an object of its own site, so the three
affine-chart results of
`StacksFrontier/AlgebraicGeometry/Spaces/CartesianChartDiagramsOfQuasicoherent.lean` apply there
and exhibit `M(W)` as the cokernel of a map of free `𝒪_X(W)`-modules.

The presentation those three results consume is produced by
`AlgebraicGeometry.Space.nonempty_presentation_modulePullback_chartToSpace_of_isAffine`, whose
index types already live in the universe `u` of the structure rings: the descent from the
universe `u + 1` in which `SheafOfModules.HasGlobalPresentation` indexes its coproducts is
carried out by `Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation`, which
replaces an index type by the *set* of global sections the structural inclusions name and so
needs the site to be essentially small in the universe of the sections.  The small étale site of
a chart space is.

## Main results

* `AlgebraicGeometry.Space.isTerminalIdEtaleChart`: **the identity chart of the algebraic space
  represented by a scheme over the base is a terminal object of its small étale site.**  Applied
  to the object underlying an étale chart `W` of `X` this is the terminal object of the small
  étale site of the chart space of `W`; with
  `Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` it makes the sections over it
  the global sections of the chart-space restriction.
* `AlgebraicGeometry.Space.nonempty_presentation_etaleModulePullback_chartToSpace_of_isAffine`:
  the restriction of a quasi-coherent `𝒪_X`-module to the chart space of an affine étale chart
  admits a `SheafOfModules.Presentation`, in the étale-restriction reading
  `AlgebraicGeometry.Space.etaleModulePullback` of the pullback.
* `AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`: **the sections of a
  quasi-coherent `𝒪_X`-module over an affine étale chart are the cokernel of the sections of the
  presenting map of a presentation of its chart-space restriction**, the generators and the
  relations being surjective on sections over the identity chart.
* `AlgebraicGeometry.Space.preservesColimitsOfSize_modulePullback`: the pullback of modules of
  Stacks 03LU preserves colimits indexed in the universe of the structure rings, being a left
  adjoint, and
  `AlgebraicGeometry.Space.presentationModulePullback`: **a presentation transports along the
  pullback of modules, with the same index types** — `Mathlib`'s
  `SheafOfModules.Presentation.map` applied to that functor and to the inverse-image comparison
  `AlgebraicGeometry.Space.modulePullbackUnitIso` of the structure sheaves.  The equality of the
  index types is `presentationModulePullback_generators_I` and
  `presentationModulePullback_relations_I`, both `rfl`.

## Implementation notes

*The étale-restriction reading of the pullback is used rather than
`AlgebraicGeometry.Space.modulePullback`.*  The two are isomorphic by Stacks 03LW
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), and the existing producer is
stated for `modulePullback`, but only for the étale reading are the sections over the identity
chart *definitionally* the sections over `W`:
`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart` is `rfl`,
whereas the same statement for `modulePullback` is not — a consumer reading the cokernel as a
module of sections of `M` would have to transport.  So the presentation is transported once,
here, rather than at every use.

*Why both existence statements are phrased with `Nonempty.elim` rather than `obtain`.*
Destructing the `Nonempty` while the goal is the three-fold conjunction forces the motive
abstraction to traverse the whole goal, and that does not finish inside the heartbeat budget;
`Nonempty.elim` has a constant motive, and the conjunction is then assembled with the
presentation as a local variable.  Neither the transport along Stacks 03LW nor the three
affine-chart results is itself expensive.

*No canonicity is claimed for the presentation.*  Only its existence is asserted, which is what
a consumer comparing two modules up to isomorphism — `Module.Finite`, a Fitting ideal, a
`Nonempty (… ≃ₗ …)` — needs.  Nothing here says that the index types are finite: `M` is not
assumed of finite type, and the index types produced by the universe descent are sets of global
sections, not chosen generators.

### Not proved here

The predicate `AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams` of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingIdealPullback.lean` — the affine-chart description
of a module pullback *across* a morphism of algebraic spaces, carried as a hypothesis at seven
sites — is **not** discharged here.  What this file supplies is one of its two inputs: the
right-exact sequence of `𝒪(chart)`-modules on each side of a chart diagram.  Deriving the
predicate from them additionally needs the two sequences to have the *same* index types and the
identification of the comparison at a free module with `TensorProduct.finsuppScalarRight`
through `AlgebraicGeometry.Space.freeSectionsIsoOfIsAffine`.  The first of those two is
`presentationModulePullback` below, applied to the pullback along
`AlgebraicGeometry.Space.chartSpaceMapOver` of a morphism of chart schemes over the morphism of
spaces and then transported along
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`; the second, and the comparison
map itself, are not done here.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The identity chart is terminal -/

/-- **The identity chart of the algebraic space represented by a scheme over the base is a
terminal object of its small étale site.**

An étale chart of `yoneda.obj U` is a scheme chart of `yoneda.obj U`, and the identity of
`yoneda.obj U` is terminal among those because `yoneda` is fully faithful
(`CategoryTheory.CostructuredArrow.mkIdTerminal`); the étale charts form a full subcategory of
the scheme charts, so terminality is inherited.

Read at the object underlying an étale chart `W` of an algebraic space `X`, this is the terminal
object of the small étale site of `AlgebraicGeometry.Space.chartSpace`.  Fed to
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` it says that the global
sections of a module on that chart space are its sections over the identity chart, which for the
étale reading of the chart-space restriction are the sections of the module over `W`; that is
what identifies the generating sections of the presentations below with elements of `M(W)`. -/
noncomputable def isTerminalIdEtaleChart (U : BigFppfOver B S hS) :
    IsTerminal (idEtaleChart B S hS U) :=
  IsTerminal.ofUniqueHom
    (fun A => ObjectProperty.homMk
      ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := U)).from A.obj))
    (fun _ m => ObjectProperty.hom_ext _
      ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := U)).hom_ext m.hom
        ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := U)).from _)))

/-! ### A presentation of the chart-space restriction -/

/-- **The restriction of a quasi-coherent `𝒪_X`-module to the chart space of an affine étale
chart admits a `SheafOfModules.Presentation`**, in the étale-restriction reading
`AlgebraicGeometry.Space.etaleModulePullback` of the pullback of Stacks 03LU.

This is `AlgebraicGeometry.Space.nonempty_presentation_modulePullback_chartToSpace_of_isAffine`
transported along the comparison of Stacks 03LW
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`) by
`SheafOfModules.Presentation.ofIsIso`. -/
theorem nonempty_presentation_etaleModulePullback_chartToSpace_of_isAffine
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Nonempty ((etaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).obj M).Presentation :=
  (nonempty_presentation_modulePullback_chartToSpace_of_isAffine B S hS X M hM W hW).elim
    (fun P => ⟨SheafOfModules.Presentation.ofIsIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).app M).hom P⟩)

/-! ### The sections over an affine chart as a cokernel -/

/-- **The sections of a quasi-coherent `𝒪_X`-module over an affine étale chart are the cokernel
of the sections of the presenting map of a presentation of its chart-space restriction.**

The restriction of `M` to the chart space of `W` is quasi-coherent and has a presentation `P`;
the identity chart of that chart space is affine, because its underlying scheme is the scheme
underlying `W`, so the generators and the relations of `P` are surjective on the sections over
it and the presenting map is exact with the generators there.  By
`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart` the target
of the generators over the identity chart is `M(W)`, and the three conclusions together say that
`M(W)` is the cokernel of a map of free `𝒪_X(W)`-modules. -/
theorem exists_presentation_rightExact_app_idEtaleChart
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    ∃ P : ((etaleModulePullback B S hS (chartToSpace B S hS X W)
            (isEtale_chartToSpace B S hS X W)).obj M).Presentation,
      Function.Surjective (P.generators.π.val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj W)))) ∧
      Function.Surjective (P.relations.π.val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj W)))) ∧
      Function.Exact ((P.relations.π ≫ kernel.ι P.generators.π).val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj W))))
        (P.generators.π.val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj W)))) := by
  have hq : ((etaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W) M hM
  refine (nonempty_presentation_etaleModulePullback_chartToSpace_of_isAffine
    B S hS X M hM W hW).elim (fun P => ⟨P, ?_, ?_, ?_⟩)
  · exact surjective_generators_app_of_isAffine B S hS (chartSpace B S hS X W).1
      (chartSpace B S hS X W).2 hq P _ hW
  · exact surjective_relations_app_of_isAffine B S hS (chartSpace B S hS X W).1
      (chartSpace B S hS X W).2 hq P _ hW
  · exact exact_app_of_presentation B S hS (chartSpace B S hS X W).1
      (chartSpace B S hS X W).2 hq P _ hW

/-! ### Transporting a presentation along a pullback of modules -/

variable {X}

/-- The pullback of modules of Stacks 03LU preserves colimits indexed in the universe `u` of the
structure rings: it is the left adjoint of `AlgebraicGeometry.Space.modulePullbackAdjunction`,
so it preserves colimits indexed in the universe `u + 1` of the small étale sites, and
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` descends the index universe.

Not an instance: the shrinking step has to be given its index universes explicitly, which
instance search will not do. -/
theorem preservesColimitsOfSize_modulePullback {Z : AlgebraicSpaces B S hS} (a : X ⟶ Z) :
    PreservesColimitsOfSize.{u, u} (modulePullback B S hS a) :=
  have : (modulePullback B S hS a).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS a⟩⟩
  preservesColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- **A presentation transports along the pullback of modules of Stacks 03LU, with the same
index types.**

`SheafOfModules.Presentation.map` carries a presentation along any colimit-preserving functor
of sheaves of modules which carries the structure sheaf to the structure sheaf; for the pullback
of Stacks 03LU the first is `preservesColimitsOfSize_modulePullback` and the second is
`AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
noncomputable def presentationModulePullback {Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    {M : Modules.{u, u} B S hS Z.1 Z.2} (P : M.Presentation) :
    ((modulePullback B S hS a).obj M).Presentation :=
  have := preservesColimitsOfSize_modulePullback B S hS a
  P.map (modulePullback B S hS a) (modulePullbackUnitIso B S hS a).symm

/-- The transported presentation has the same generators index type. -/
theorem presentationModulePullback_generators_I {Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    {M : Modules.{u, u} B S hS Z.1 Z.2} (P : M.Presentation) :
    (presentationModulePullback B S hS a P).generators.I = P.generators.I := rfl

/-- The transported presentation has the same relations index type. -/
theorem presentationModulePullback_relations_I {Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    {M : Modules.{u, u} B S hS Z.1 Z.2} (P : M.Presentation) :
    (presentationModulePullback B S hS a P).relations.I = P.relations.I := rfl

end AlgebraicGeometry.Space

end
