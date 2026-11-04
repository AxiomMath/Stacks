module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent

/-!
# Additions to `ChartRestrictionSections`

Declarations this development adds alongside
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections`, kept in their own module so that
the base file is unchanged: 2 declaration(s) that the base file does not have, with the section
variables, namespaces and options they are stated in.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The chart restriction before sheafification is already a sheaf -/

/-! ### The sections -/

/-- **The sections of an `𝒪_X`-module over an étale chart are the global sections of its
unsheafified chart restriction**, as additive groups.

The sections of `AlgebraicGeometry.Space.chartRestrictionSheaf` over the open `⊤` of the chart's
scheme are, by `AlgebraicGeometry.Space.chartRestrictionSheaf_obj` and on the nose, the sections
of the module over the chart `⊤` cuts out, with the universe of the sections raised; that chart
is the chart itself by `AlgebraicGeometry.Space.isIso_chartOpensTopHom`, and the universe lift is
undone by `AddEquiv.ulift`. -/
noncomputable def chartRestrictionSheafTopSectionsEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (M.val.obj (op A) : Type u) ≃+ (Γ(chartRestrictionSheaf B S hS X M A, ⊤) : Type u) :=
  (M.val.presheaf.mapIso
      (asIso (chartOpensTopHom B S hS X A)).op).addCommGroupIsoToAddEquiv.trans
    AddEquiv.ulift.symm

/-- **The global sections of the chart restriction of an `𝒪_X`-module are its sections over the
chart**, canonically and with no hypothesis on the module.

The chart restriction needs no sheafification
(`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`) and the global sections of
the unsheafified restriction are the sections over the chart
(`AlgebraicGeometry.Space.chartRestrictionSheafTopSectionsEquiv`).  Both steps are named
isomorphisms — the first is a sheafification counit, the second is a presheaf acting on an
invertible morphism of charts — so this identification is determined by `M` and `A` and carries
no choice.

This is the route to the sections of a module on an algebraic space which does **not** pass
through a base change of the restriction: the restriction of Stacks 03M0 is compatible with the
inverse image of Stacks 03LW only for a *quasi-coherent* module and through
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, whereas the sections over a chart are
plain evaluation of a presheaf.  It is what the restriction map of the backward functor of
Stacks 06WT is built from; see the implementation notes. -/
noncomputable def restrictToChartTopSectionsEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (Γ(restrictToChart B S hS X.2 M A, ⊤) : Type u) ≃+ (M.val.obj (op A) : Type u) :=
  ((moduleGlobalSections (chartScheme A)).mapIso
        (restrictToChartIsoChartRestrictionSheaf B S hS X M A)).toLinearEquiv.toAddEquiv.trans
    (chartRestrictionSheafTopSectionsEquiv B S hS X M A).symm

/-! ### Quasi-coherence -/

end AlgebraicGeometry.Space

end
