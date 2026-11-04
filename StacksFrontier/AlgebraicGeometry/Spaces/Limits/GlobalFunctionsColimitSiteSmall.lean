module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Global functions on a limit of algebraic spaces, under a smallness hypothesis

Stacks 07SI for the structure sheaf, in the strictly functorial form
`AlgebraicGeometry.Space.DescentSituation.IsGlobalFunctionsColimit`, under the hypotheses
`AlgebraicGeometry.Space.IsSiteSmall` and `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `DescentSituation.exists_transition_eq_of_projection_eq_of_siteContainsBaseChangeLimits`
* `DescentSituation.exists_transition_eq_of_projection_eq`
* `DescentSituation.exists_stage_globalFunctionsMap_eq_of_siteContainsBaseChangeLimits`
* `DescentSituation.exists_stage_globalFunctionsMap_eq`
* `DescentSituation.isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits`
* `DescentSituation.isGlobalFunctionsColimit_of_isSiteSmall`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### Chart restriction against pullback of global functions -/

section ChartCompatibility

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end ChartCompatibility

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-! ### The assertion of Stacks 07SI for the structure sheaf -/

/-! ### Transport to the limit-situation machinery -/

section Transport

variable {B' : BigFppfSite.{u}} {S' : Scheme.{u}} {hS' : B'.Contains S'}
  {hZ' : B'.Contains (⊤_ Scheme.{u})} {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
  (E : DescentSituation B' S' hS' hZ' J)

end Transport

/-! ### The separation clause, via morphisms to the affine line -/

section Wiring

variable {B : BigFppfSite.{u}} {I : Type u}
  {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
  [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The separation clause of Stacks 07SI for the structure sheaf, under the chapter's standing
convention.** Two global regular functions on a stage with the same image on the limit already
agree at a later stage. This is
`AlgebraicGeometry.Space.DescentSituation.exists_transition_eq_of_projection_eq` with the
smallness of the system replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. -/
theorem exists_transition_eq_of_projection_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (i : I) (s s' : globalFunctions' B S hS (D.stage i).obj)
    (h : globalFunctionsMap B S hS (D.projection i) s
      = globalFunctionsMap B S hS (D.projection i) s') :
    ∃ (j : I) (hij : i ≤ j),
      globalFunctionsMap B S hS (D.transition hij) s
        = globalFunctionsMap B S hS (D.transition hij) s' := by
  have : Nonempty I := ⟨D.base⟩
  have hlim : D.limitCone.π.app (op i) ≫
        (globalFunctionsHomEquiv B S hS (D.stage i) s).hom
      = D.limitCone.π.app (op i) ≫
        (globalFunctionsHomEquiv B S hS (D.stage i) s').hom := by
    have e : D.projection i ≫ globalFunctionsHomEquiv B S hS (D.stage i) s
        = D.projection i ≫ globalFunctionsHomEquiv B S hS (D.stage i) s' := by
      rw [← globalFunctionsHomEquiv_natural, ← globalFunctionsHomEquiv_natural, h]
    exact congrArg (fun f : D.limitSpace ⟶ affineLineSpace B S hS => f.hom) e
  obtain ⟨k, a, hka⟩ :=
    exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ
    D.system D.limitCone D.isLimit hconv
    (fun m => D.algebraicSpace m.unop) (fun m => D.quasiCompact m.unop)
    (fun m => D.quasiSeparated m.unop) (fun {_ _} g => D.transition_affine g)
    D.limitAlgebraicSpace (affineLineSpace B S hS).property
    (isAlgebraicSpace_terminal B S hS) (terminal.from _)
    (isLocallyOfFinitePresentation_affineLineSpace B S hS) (op i)
    (globalFunctionsHomEquiv B S hS (D.stage i) s).hom
    (globalFunctionsHomEquiv B S hS (D.stage i) s').hom hlim (terminal.hom_ext _ _)
  refine ⟨k.unop, leOfHom a.unop, ?_⟩
  apply (globalFunctionsHomEquiv B S hS (D.stage k.unop)).injective
  rw [globalFunctionsHomEquiv_natural, globalFunctionsHomEquiv_natural]
  apply CategoryTheory.ObjectProperty.hom_ext
  have hmap : D.system.map a = D.system.map (homOfLE (leOfHom a.unop)).op :=
    congrArg D.system.map (Subsingleton.elim _ _)
  show D.system.map (homOfLE (leOfHom a.unop)).op ≫
        (globalFunctionsHomEquiv B S hS (D.stage i) s).hom
      = D.system.map (homOfLE (leOfHom a.unop)).op ≫
        (globalFunctionsHomEquiv B S hS (D.stage i) s').hom
  rw [← hmap]
  exact hka

/-- **The separation clause of Stacks 07SI for the structure sheaf.** Two global regular
functions on a stage with the same image on the limit already agree at a later stage.

Global regular functions on an algebraic space are its morphisms to the affine line, naturally
in the space (`AlgebraicGeometry.Space.globalFunctionsHomEquiv` and
`AlgebraicGeometry.Space.globalFunctionsHomEquiv_natural`), so this is the statement that two
morphisms from a stage to `𝔸¹_S` agreeing over the limit agree at a later stage. That is
`AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving_of_isSiteSmall`, whose target
hypothesis is discharged by
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_affineLineSpace` and whose relative
hypothesis `hbase` is free, the base being the terminal presheaf. Its remaining hypotheses are
the fields of the descent situation, read at `Iᵒᵖ`, together with smallness of the system for
the site.

**The terminal target is load-bearing, not cosmetic.** Both approximation results are
*relative*: `AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving_of_isSiteSmall`
asks
`hbase : r ≫ φ = s ≫ φ` over and above agreement at the limit, and
`.exists_stage_map_of_relativelyLimitPreserving` asks the corresponding `hsq`. Those are
discharged here by `CategoryTheory.Limits.terminal.hom_ext`, which is available *only* because
the target of `φ` is terminal. Anyone tempted to restate these clauses over a non-terminal
base must supply those hypotheses; they do not come for free.

The smallness hypothesis `hb` is a separate binder because
`AlgebraicGeometry.Space.DescentSituation` carries no such field. It is met either by the
cofinality bound on the index that Stacks 07SF asks for, through
`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op`, or by the transition morphisms of the
system being monomorphisms, which asks nothing of the index. It forces `I : Type u`, since at
a free index universe the cardinality of the index is not comparable with the cutoff,
`Cardinal.{v}` against `Cardinal.{u}`.

An alternative formulation would take the target as `yoneda.obj (Over.mk (𝟙 (B.obj hS)))`
with `AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`, for which the finite-presentation
hypothesis is `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map` directly and
no isomorphism transport is needed. It is not used here only because the `terminal.from`
spelling is what `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_affineLineSpace`
already provides, and that transport is paid once inside it rather than at each use. -/
theorem exists_transition_eq_of_projection_eq (hb : IsSiteSmall B S hS D.system)
    (i : I) (s s' : globalFunctions' B S hS (D.stage i).obj)
    (h : globalFunctionsMap B S hS (D.projection i) s
      = globalFunctionsMap B S hS (D.projection i) s') :
    ∃ (j : I) (hij : i ≤ j),
      globalFunctionsMap B S hS (D.transition hij) s
        = globalFunctionsMap B S hS (D.transition hij) s' :=
  have : Nonempty I := ⟨D.base⟩
  D.exists_transition_eq_of_projection_eq_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.system hb) i s s' h

/-- **The surjectivity clause of Stacks 07SI for the structure sheaf, under the chapter's
standing convention.** Every global regular function on the limit is the pullback of one from a
stage. This is `AlgebraicGeometry.Space.DescentSituation.exists_stage_globalFunctionsMap_eq` with
the smallness of the system replaced by
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. -/
theorem exists_stage_globalFunctionsMap_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (t : globalFunctions' B S hS D.limitSpace.obj) :
    ∃ (j : I) (s : globalFunctions' B S hS (D.stage j).obj),
      globalFunctionsMap B S hS (D.projection j) s = t := by
  have : Nonempty I := ⟨D.base⟩
  obtain ⟨j, g, k, a, a', h₁, -⟩ :=
    exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ
    D.system D.limitCone D.isLimit hconv
    (fun m => D.algebraicSpace m.unop) (fun m => D.quasiCompact m.unop)
    (fun m => D.quasiSeparated m.unop) (fun {_ _} q => D.transition_affine q)
    D.limitAlgebraicSpace (affineLineSpace B S hS).property
    (isAlgebraicSpace_terminal B S hS) (terminal.from _)
    (isLocallyOfFinitePresentation_affineLineSpace B S hS)
    (globalFunctionsHomEquiv B S hS D.limitSpace t).hom (op D.base)
    (terminal.from _) (terminal.hom_ext _ _)
  refine ⟨k.unop, (globalFunctionsHomEquiv B S hS (D.stage k.unop)).symm
    (ObjectProperty.homMk (D.system.map a ≫ g)), ?_⟩
  apply (globalFunctionsHomEquiv B S hS D.limitSpace).injective
  rw [globalFunctionsHomEquiv_natural, Equiv.apply_symm_apply]
  apply CategoryTheory.ObjectProperty.hom_ext
  exact h₁

/-- **The surjectivity clause of Stacks 07SI for the structure sheaf.** Every global regular
function on the limit is the pullback of one from a stage.

Read through `AlgebraicGeometry.Space.globalFunctionsHomEquiv` this is the statement that a
morphism `X ⟶ 𝔸¹_S` out of the limit factors through a stage, which is
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving_of_isSiteSmall`. Its
conclusion
produces a stage `j`, a morphism `t` there, a further stage `k` and transitions `a`, `a'`; the
factorisation wanted here is through `k`, by the morphism `D.map a ≫ t`, which is what the
first conjunct asserts. The second conjunct is the relative condition and is discharged by
`CategoryTheory.Limits.terminal.hom_ext`, as is the input `hsq`; see the note on the terminal
target in `exists_transition_eq_of_projection_eq`. -/
theorem exists_stage_globalFunctionsMap_eq (hb : IsSiteSmall B S hS D.system)
    (t : globalFunctions' B S hS D.limitSpace.obj) :
    ∃ (j : I) (s : globalFunctions' B S hS (D.stage j).obj),
      globalFunctionsMap B S hS (D.projection j) s = t :=
  have : Nonempty I := ⟨D.base⟩
  D.exists_stage_globalFunctionsMap_eq_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.system hb) t

/-- **Stacks 07SI for the structure sheaf, under the chapter's standing convention**: the ring of
global regular functions of the limit of a descent situation is the filtered colimit of the
rings of global regular functions of the stages.

The source asks nothing of the index; it works under the convention of Section 70.2 (tag 07SD)
that every ring considered has its spectrum in the big fppf site, which for this system is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` — the limits of the affine charts of the
system lie in the site. That convention is what is assumed here, and it is strictly weaker than
the smallness hypothesis of
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_of_isSiteSmall`
(`AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`).

Some such hypothesis is needed. Over a field `k`, let `F` be an extension field of cardinality at
least the cutoff of the site, and index the stages by the finite subsets of `F`, the stage at a
subset being the spectrum of the subfield it generates. The limit of the system in the site is
the empty space, because a nonempty object of the site has a ring of global functions too small
to receive `F`; its ring of global functions is zero, while the colimit of the stage rings is
`F`. Here the ring considered, `F`, has no spectrum in the site, so the convention fails. -/
theorem isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    D.IsGlobalFunctionsColimit :=
  D.isGlobalFunctionsColimit_iff.mpr
    ⟨D.exists_stage_globalFunctionsMap_eq_of_siteContainsBaseChangeLimits hconv,
      D.exists_transition_eq_of_projection_eq_of_siteContainsBaseChangeLimits hconv⟩

/-- **Stacks 07SI for the structure sheaf**, for a descent situation whose index set lies in
the universe of the site: the ring of global regular functions of the limit is the filtered
colimit of the rings of global regular functions of the stages.

Both clauses are instances of the approximation of morphisms into a target locally of finite
presentation, the target being the affine line and the dictionary
`AlgebraicGeometry.Space.globalFunctionsHomEquiv`; see
`exists_stage_globalFunctionsMap_eq` and `exists_transition_eq_of_projection_eq`.

The hypothesis `hb` is smallness of the system for the site. It cannot be dropped on this
route: `AlgebraicGeometry.Space.DescentSituation` carries no such field, and the approximation
results need it. Under its cofinality alternative it is the size bound of Stacks 07SF; under
its other alternative it asks nothing of the index and only that the transition morphisms be
monomorphisms. -/
theorem isGlobalFunctionsColimit_of_isSiteSmall (hb : IsSiteSmall B S hS D.system) :
    D.IsGlobalFunctionsColimit :=
  have : Nonempty I := ⟨D.base⟩
  D.isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.system hb)

end Wiring

end DescentSituation

end AlgebraicGeometry.Space

end
