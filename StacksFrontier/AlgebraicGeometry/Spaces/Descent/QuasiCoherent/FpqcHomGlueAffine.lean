module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcHomGlueUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartDiagramsOfQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom
public import StacksFrontier.AlgebraicGeometry.Descent.Module.HomDescentFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartLocalization

/-!
# Fpqc descent of morphisms of quasi-coherent modules over an affine represented base

Let `T` be an affine object of the big fppf site of `S`, let `(g j : U j ⟶ T)` be a finite
family of affine objects whose rings form a faithfully flat family over the ring of `T`, and let
`M`, `N` be quasi-coherent modules on the algebraic space represented by `T`.  This file proves
that a family of homomorphisms `(g j)^*M ⟶ (g j)^*N` agreeing on the overlaps is the family of
inverse images of one homomorphism `M ⟶ N`.  This is the affine case of the gluing half of the
full-faithfulness clause of Stacks 04W8, and its proof is that of Stacks 023S: on sections over
the identity charts the inverse images are base changes of modules (Stacks 03DX (2)), and the
statement becomes descent of linear maps along a faithfully flat ring map (Stacks 023M).

## Main definitions

* `AlgebraicGeometry.Space.reprChartSection`, `AlgebraicGeometry.Space.reprRestrict` and
  `AlgebraicGeometry.Space.reprBaseChange`: the chart section, the pullback of regular
  functions and the base-change comparison of an inverse image along a morphism of represented
  algebraic spaces, all read over the identity charts.

## Main results

* `AlgebraicGeometry.Space.reprChartSection_reprBaseChange`: the base-change comparison is
  compatible with a further inverse image, read through any comparison intertwining the chart
  sections.
* `AlgebraicGeometry.Space.exists_hom_of_linearMap_of_isTerminal`: a linear map of the sections
  over an affine terminal chart of a quasi-coherent module is induced by a morphism of modules.
* `AlgebraicGeometry.Space.exists_hom_of_reprFamily`: **the affine case of descent of
  morphisms**, for a faithfully flat finite family whose overlap rings are pushouts.
* `AlgebraicGeometry.Space.faithfullyFlat_reprFamily` and
  `AlgebraicGeometry.Space.bijective_productMap_reprRestrict`: the two ring-theoretic inputs,
  from a finite flat jointly surjective family of affine schemes and from fibre products of
  affine schemes.

## Implementation notes

All sections are written over the identity charts `AlgebraicGeometry.Space.idEtaleChart`, never
over the charts `d.U` of a chart diagram: the two are definitionally equal, but the kernel does
not identify the module structures on sections spelled in the two ways in reasonable time.  The
wrappers `AlgebraicGeometry.Space.reprChartSection` and `AlgebraicGeometry.Space.reprBaseChange`
fix the spelling once, and every later statement is phrased through them.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (reprSpaceMap)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The diagram of identity charts over a morphism of represented algebraic spaces. -/
abbrev reprIdChartDiagram {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    ChartDiagram B S hS (representedAlgebraicSpace B S hS T').1
      (representedAlgebraicSpace B S hS T).1 (reprSpaceMap B S hS g).hom where
  U := idEtaleChart B S hS T'
  V := idEtaleChart B S hS T
  g := g
  comm := (Category.id_comp _).trans (Category.comp_id _).symm

/-- The morphism of represented algebraic spaces of a composite is the composite. -/
theorem reprSpaceMap_comp {T'' T' T : BigFppfOver B S hS} (k : T'' ⟶ T') (g : T' ⟶ T) :
    reprSpaceMap B S hS k ≫ reprSpaceMap B S hS g = reprSpaceMap B S hS (k ≫ g) :=
  ObjectProperty.hom_ext _ (yoneda.map_comp k g).symm

/-- A section of a module over the identity chart of a represented algebraic space, as a global
section. -/
abbrev reprGlobalSection {T : BigFppfOver B S hS}
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2)
    (s : N.val.obj (op (idEtaleChart B S hS T))) : N.sections :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N
    (isTerminalIdEtaleChart B S hS T)).symm s

/-- The global section attached to a section over the identity chart has that value there. -/
theorem reprGlobalSection_val {T : BigFppfOver B S hS}
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2)
    (s : N.val.obj (op (idEtaleChart B S hS T))) :
    (reprGlobalSection B S hS N s).val (op (idEtaleChart B S hS T)) = s :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N
    (isTerminalIdEtaleChart B S hS T)).apply_symm_apply s

/-- **The chart section along a composite of represented morphisms**, read through the
composition comparison of Stacks 03LU. -/
theorem modulePullbackChartSection_reprIdChartDiagram_comp {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T)
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2)
    (s : N.val.obj (op (idEtaleChart B S hS T))) :
    modulePullbackChartSection B S hS (reprSpaceMap B S hS k) _ (reprIdChartDiagram B S hS k)
        (modulePullbackChartSection B S hS (reprSpaceMap B S hS g) N
          (reprIdChartDiagram B S hS g) s) =
      ((modulePullbackTriangle B S hS (reprSpaceMap_comp B S hS k g)).hom.app N).val.app
        (op (idEtaleChart B S hS T''))
        (modulePullbackChartSection B S hS (reprSpaceMap B S hS (k ≫ g)) N
          (reprIdChartDiagram B S hS (k ≫ g)) s) := by
  have h1 := modulePullbackSections_val B S hS (reprSpaceMap B S hS g) N
    (reprGlobalSection B S hS N s) (reprIdChartDiagram B S hS g)
  have h2 := modulePullbackSections_val B S hS (reprSpaceMap B S hS k) _
    (modulePullbackSections B S hS (reprSpaceMap B S hS g) N (reprGlobalSection B S hS N s))
    (reprIdChartDiagram B S hS k)
  have h3 := modulePullbackSections_val B S hS (reprSpaceMap B S hS (k ≫ g)) N
    (reprGlobalSection B S hS N s) (reprIdChartDiagram B S hS (k ≫ g))
  have h4 := congrArg (fun σ => σ.val (op (idEtaleChart B S hS T'')))
    (sectionsMap_modulePullbackSections_triangle B S hS (reprSpaceMap B S hS k)
      (reprSpaceMap B S hS g) (reprSpaceMap_comp B S hS k g) N (reprGlobalSection B S hS N s))
  have hv := reprGlobalSection_val B S hS N s
  have e1 : modulePullbackChartSection B S hS (reprSpaceMap B S hS g) N
      (reprIdChartDiagram B S hS g) s =
      (modulePullbackSections B S hS (reprSpaceMap B S hS g) N
        (reprGlobalSection B S hS N s)).val (op (idEtaleChart B S hS T')) :=
    (congrArg (modulePullbackChartSection B S hS (reprSpaceMap B S hS g) N
      (reprIdChartDiagram B S hS g)) hv.symm).trans h1.symm
  have e3 : (modulePullbackSections B S hS (reprSpaceMap B S hS (k ≫ g)) N
        (reprGlobalSection B S hS N s)).val (op (idEtaleChart B S hS T'')) =
      modulePullbackChartSection B S hS (reprSpaceMap B S hS (k ≫ g)) N
        (reprIdChartDiagram B S hS (k ≫ g)) s :=
    h3.trans (congrArg (modulePullbackChartSection B S hS (reprSpaceMap B S hS (k ≫ g)) N
      (reprIdChartDiagram B S hS (k ≫ g))) hv)
  refine (congrArg (modulePullbackChartSection B S hS (reprSpaceMap B S hS k) _
    (reprIdChartDiagram B S hS k)) e1).trans (h2.symm.trans (h4.symm.trans ?_))
  exact congrArg (fun z => ((modulePullbackTriangle B S hS (reprSpaceMap_comp B S hS k g)).hom.app
    N).val.app (op (idEtaleChart B S hS T'')) z) e3

/-- The morphism of represented algebraic spaces of a composite, for a composite given by an
equation. -/
theorem reprSpaceMap_comp_eq {T'' T' T : BigFppfOver B S hS} (k : T'' ⟶ T') (g : T' ⟶ T)
    {l : T'' ⟶ T} (hl : k ≫ g = l) :
    reprSpaceMap B S hS k ≫ reprSpaceMap B S hS g = reprSpaceMap B S hS l :=
  (reprSpaceMap_comp B S hS k g).trans (congrArg (reprSpaceMap B S hS) hl)

/-- **The chart section along a composite of represented morphisms**, for a composite given by
an equation. -/
theorem modulePullbackChartSection_reprIdChartDiagram_triangle {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2)
    (s : N.val.obj (op (idEtaleChart B S hS T))) :
    modulePullbackChartSection B S hS (reprSpaceMap B S hS k) _ (reprIdChartDiagram B S hS k)
        (modulePullbackChartSection B S hS (reprSpaceMap B S hS g) N
          (reprIdChartDiagram B S hS g) s) =
      ((modulePullbackTriangle B S hS (reprSpaceMap_comp_eq B S hS k g hl)).hom.app N).val.app
        (op (idEtaleChart B S hS T''))
        (modulePullbackChartSection B S hS (reprSpaceMap B S hS l) N
          (reprIdChartDiagram B S hS l) s) := by
  subst hl
  exact modulePullbackChartSection_reprIdChartDiagram_comp B S hS k g N s

/-- Pullback of regular functions along identity-chart diagrams composes. -/
theorem chartDiagramRestrict_reprIdChartDiagram_comp {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    (a : chartRing B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2 (idEtaleChart B S hS T)) :
    chartDiagramRestrict B S hS (reprSpaceMap B S hS k) (reprIdChartDiagram B S hS k)
        (chartDiagramRestrict B S hS (reprSpaceMap B S hS g) (reprIdChartDiagram B S hS g) a) =
      chartDiagramRestrict B S hS (reprSpaceMap B S hS l) (reprIdChartDiagram B S hS l) a := by
  subst hl
  change ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map g).op) ≫ (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map k).op)).hom a = ((forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (k ≫ g)).op)).hom a
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← Functor.map_comp]

/-- The ring of regular functions on the identity chart of a represented algebraic space. -/
abbrev reprRing (T : BigFppfOver B S hS) : Type u :=
  chartRing B S hS (representedAlgebraicSpace B S hS T).1 (representedAlgebraicSpace B S hS T).2
    (idEtaleChart B S hS T)

/-- The sections of a module on a represented algebraic space over the identity chart. -/
abbrev reprSec {T : BigFppfOver B S hS}
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) : Type u :=
  M.val.obj (op (idEtaleChart B S hS T))

/-- The chart section of an inverse image along a represented morphism, over identity charts. -/
def reprChartSection {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (s : reprSec B S hS M) :
    reprSec B S hS ((modulePullback B S hS (reprSpaceMap B S hS g)).obj M) :=
  (modulePullbackSections B S hS (reprSpaceMap B S hS g) M (reprGlobalSection B S hS M s)).val
    (op (idEtaleChart B S hS T'))

/-- The chart section over identity charts is the chart section of the unit of Stacks 03D7. -/
theorem reprChartSection_eq {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (s : reprSec B S hS M) :
    reprChartSection B S hS g M s =
      modulePullbackChartSection B S hS (reprSpaceMap B S hS g) M (reprIdChartDiagram B S hS g) s :=
  (modulePullbackSections_val B S hS (reprSpaceMap B S hS g) M
    (reprGlobalSection B S hS M s) (reprIdChartDiagram B S hS g)).trans
    (congrArg (modulePullbackChartSection B S hS (reprSpaceMap B S hS g) M
      (reprIdChartDiagram B S hS g)) (reprGlobalSection_val B S hS M s))

/-- Pullback of regular functions along a represented morphism, over identity charts. -/
abbrev reprRestrict {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    reprRing B S hS T →+* reprRing B S hS T' :=
  chartDiagramRestrict B S hS (reprSpaceMap B S hS g) (reprIdChartDiagram B S hS g)

/-- The chart section over identity charts is semilinear over pullback of regular functions. -/
theorem reprChartSection_smul {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (r : reprRing B S hS T) (s : reprSec B S hS M) :
    reprChartSection B S hS g M (r • s) = reprRestrict B S hS g r • reprChartSection B S hS g M s :=
  (reprChartSection_eq B S hS g M _).trans ((modulePullbackChartSection_smul B S hS _ M
    (reprIdChartDiagram B S hS g) r s).trans
    (congrArg (fun z => reprRestrict B S hS g r • z) (reprChartSection_eq B S hS g M s).symm))

/-- The chart section over identity charts is additive. -/
theorem reprChartSection_add {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (s t : reprSec B S hS M) :
    reprChartSection B S hS g M (s + t) =
      reprChartSection B S hS g M s + reprChartSection B S hS g M t :=
  (reprChartSection_eq B S hS g M _).trans ((modulePullbackChartSection_add B S hS _ M
    (reprIdChartDiagram B S hS g) s t).trans (by rw [reprChartSection_eq, reprChartSection_eq]))

/-- The chart section over identity charts carries zero to zero. -/
theorem reprChartSection_zero {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) :
    reprChartSection B S hS g M 0 = 0 := by
  have h := reprChartSection_add B S hS g M 0 0
  rw [add_zero] at h
  exact add_eq_left.1 h.symm

/-- The chart section over identity charts is natural in the module. -/
theorem reprChartSection_map {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M M' : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (a : M ⟶ M') (s : reprSec B S hS M) :
    ((modulePullback B S hS (reprSpaceMap B S hS g)).map a).val.app
        (op (idEtaleChart B S hS T')) (reprChartSection B S hS g M s) =
      reprChartSection B S hS g M' (a.val.app (op (idEtaleChart B S hS T)) s) :=
  by rw [reprChartSection_eq, reprChartSection_eq]
     exact modulePullbackChartSection_map B S hS _ M a (reprIdChartDiagram B S hS g) s

/-- The composition comparison of Stacks 03LU at a module, along a triangle of represented
morphisms, with its target written as an iterated inverse image. -/
def reprTriangle {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) :
    (modulePullback B S hS (reprSpaceMap B S hS l)).obj N ≅
      (modulePullback B S hS (reprSpaceMap B S hS k)).obj
        ((modulePullback B S hS (reprSpaceMap B S hS g)).obj N) :=
  (modulePullbackTriangle B S hS (reprSpaceMap_comp_eq B S hS k g hl)).app N

/-- The chart sections along a composite of represented morphisms, read through the composition
comparison of Stacks 03LU. -/
theorem reprChartSection_triangle {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (s : reprSec B S hS N) :
    reprChartSection B S hS k _ (reprChartSection B S hS g N s) =
      (reprTriangle B S hS k g hl N).hom.val.app
        (op (idEtaleChart B S hS T'')) (reprChartSection B S hS l N s) := by
  rw [reprChartSection_eq, reprChartSection_eq, reprChartSection_eq]
  exact modulePullbackChartSection_reprIdChartDiagram_triangle B S hS k g hl N s

/-- Pullback of regular functions along identity charts composes. -/
theorem reprRestrict_comp {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l) (a : reprRing B S hS T) :
    reprRestrict B S hS k (reprRestrict B S hS g a) = reprRestrict B S hS l a :=
  chartDiagramRestrict_reprIdChartDiagram_comp B S hS k g hl a

/-- The algebra structure on the ring of a represented space over that of its target. -/
abbrev reprAlgebra {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    Algebra (reprRing B S hS T) (reprRing B S hS T') :=
  chartDiagramAlgebra B S hS (reprSpaceMap B S hS g) (reprIdChartDiagram B S hS g)

/-- The base-change comparison over identity charts. -/
def reprBaseChange {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) :
    letI := reprAlgebra B S hS g
    TensorProduct (reprRing B S hS T) (reprRing B S hS T') (reprSec B S hS M) →ₗ[reprRing B S hS T']
      reprSec B S hS ((modulePullback B S hS (reprSpaceMap B S hS g)).obj M) :=
  letI := reprAlgebra B S hS g
  letI : Module (reprRing B S hS T)
      (reprSec B S hS ((modulePullback B S hS (reprSpaceMap B S hS g)).obj M)) :=
    Module.compHom _ (reprRestrict B S hS g)
  haveI : IsScalarTower (reprRing B S hS T) (reprRing B S hS T')
      (reprSec B S hS ((modulePullback B S hS (reprSpaceMap B S hS g)).obj M)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange _
    { toFun := reprChartSection B S hS g M
      map_add' := reprChartSection_add B S hS g M
      map_smul' := reprChartSection_smul B S hS g M }

/-- The base-change comparison carries `b ⊗ s` to `b` times the chart section of `s`. -/
theorem reprBaseChange_tmul {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (b : reprRing B S hS T') (s : reprSec B S hS M) :
    letI := reprAlgebra B S hS g
    reprBaseChange B S hS g M (b ⊗ₜ s) = b • reprChartSection B S hS g M s := rfl

/-- The base-change comparison over identity charts is the base-change comparison of the chart
diagram. -/
theorem reprBaseChange_eq {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) :
    letI := reprAlgebra B S hS g
    ∀ z, reprBaseChange B S hS g M z =
      modulePullbackChartBaseChange B S hS (reprSpaceMap B S hS g) M
        (reprIdChartDiagram B S hS g) z := by
  let := reprAlgebra B S hS g
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    rw [reprBaseChange_tmul, modulePullbackChartBaseChange_tmul, reprChartSection_eq]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The base-change comparison of a quasi-coherent module over identity charts of affine
represented algebraic spaces is bijective.** -/
theorem bijective_reprBaseChange {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (hM : M.IsQuasicoherentOnSite) :
    Function.Bijective (reprBaseChange B S hS g M) := by
  have h := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS _ M hM
    (reprIdChartDiagram B S hS g) hT' hT
  have he : (reprBaseChange B S hS g M : _ → _) =
      (modulePullbackChartBaseChange B S hS (reprSpaceMap B S hS g) M
        (reprIdChartDiagram B S hS g) : _ → _) := funext (reprBaseChange_eq B S hS g M)
  rw [he]
  exact h

/-- Pullback of regular functions along `k`, as a linear map over the ring of `T`. -/
def reprRestrictLinear {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l) :
    letI := reprAlgebra B S hS g
    letI := reprAlgebra B S hS l
    reprRing B S hS T' →ₗ[reprRing B S hS T] reprRing B S hS T'' :=
  letI := reprAlgebra B S hS g
  letI := reprAlgebra B S hS l
  { toFun := fun b => reprRestrict B S hS k b
    map_add' := fun a b => map_add _ a b
    map_smul' := fun a b => by
      change reprRestrict B S hS k (reprRestrict B S hS g a * b) =
        reprRestrict B S hS l a * reprRestrict B S hS k b
      rw [map_mul, reprRestrict_comp B S hS k g hl] }

/-- Pullback of regular functions along `k`, as a morphism of algebras over the ring of `T`. -/
def reprRestrictAlgHom {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l) :
    letI := reprAlgebra B S hS g
    letI := reprAlgebra B S hS l
    reprRing B S hS T' →ₐ[reprRing B S hS T] reprRing B S hS T'' :=
  letI := reprAlgebra B S hS g
  letI := reprAlgebra B S hS l
  { reprRestrict B S hS k with
    commutes' := fun a => reprRestrict_comp B S hS k g hl a }

section KF

variable {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    (N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2)
    (τ : (modulePullback B S hS (reprSpaceMap B S hS l)).obj N ⟶
      (modulePullback B S hS (reprSpaceMap B S hS k)).obj
        ((modulePullback B S hS (reprSpaceMap B S hS g)).obj N))
    (hτ : ∀ x, reprChartSection B S hS k _ (reprChartSection B S hS g N x) =
      τ.val.app (op (idEtaleChart B S hS T'')) (reprChartSection B S hS l N x))

/-- The base-change formula along a further represented morphism, at zero. -/
theorem reprChartSection_reprBaseChange_zero :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
    reprChartSection B S hS k _ (reprBaseChange B S hS g N 0) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) 0)) := by
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS l
  simp only [map_zero, reprChartSection_zero]

include hτ in
/-- The base-change formula along a further represented morphism, at a pure tensor. -/
theorem reprChartSection_reprBaseChange_tmul (b : reprRing B S hS T') (x : reprSec B S hS N) :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
    reprChartSection B S hS k _ (reprBaseChange B S hS g N (b ⊗ₜ x)) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) (b ⊗ₜ x))) := by
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS l
  have h2 : reprBaseChange B S hS l N
      (LinearMap.rTensor (reprSec B S hS N) (reprRestrictLinear B S hS k g hl) (b ⊗ₜ x)) =
      reprRestrict B S hS k b • reprChartSection B S hS l N x := rfl
  rw [h2, reprBaseChange_tmul, reprChartSection_smul, hτ, map_smul]

/-- The base-change formula along a further represented morphism is additive. -/
theorem reprChartSection_reprBaseChange_add
    (x y : letI := reprAlgebra B S hS g
      TensorProduct (reprRing B S hS T) (reprRing B S hS T') (reprSec B S hS N))
    (hx : letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
      reprChartSection B S hS k _ (reprBaseChange B S hS g N x) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) x)))
    (hy : letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
      reprChartSection B S hS k _ (reprBaseChange B S hS g N y) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) y))) :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
    reprChartSection B S hS k _ (reprBaseChange B S hS g N (x + y)) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) (x + y))) := by
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS l
  simp only [map_add, reprChartSection_add]
  rw [hx, hy]

include hτ in
/-- **The chart section of a base-change comparison along a further represented morphism**, for
any morphism `τ` intertwining the chart sections. -/
theorem reprChartSection_reprBaseChange
    (ζ : letI := reprAlgebra B S hS g
      TensorProduct (reprRing B S hS T) (reprRing B S hS T') (reprSec B S hS N)) :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS l
    reprChartSection B S hS k _ (reprBaseChange B S hS g N ζ) =
      τ.val.app (op (idEtaleChart B S hS T''))
        (reprBaseChange B S hS l N (LinearMap.rTensor (reprSec B S hS N)
          (reprRestrictLinear B S hS k g hl) ζ)) :=
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS l
  TensorProduct.inductionOn ζ (reprChartSection_reprBaseChange_tmul B S hS k g hl N τ hτ)
    (reprChartSection_reprBaseChange_add B S hS k g hl N τ)

end KF

/-- **The base-change comparison of the restriction of a morphism along a further represented
morphism**, for comparisons `τM`, `τN` intertwining the chart sections. -/
theorem reprBaseChange_rTensor_restrict {P U T : BigFppfOver B S hS} (p : P ⟶ U) (g : U ⟶ T)
    {r : P ⟶ T}
    (hr : p ≫ g = r)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (α : (modulePullback B S hS (reprSpaceMap B S hS g)).obj M ⟶
      (modulePullback B S hS (reprSpaceMap B S hS g)).obj N)
    (τM : (modulePullback B S hS (reprSpaceMap B S hS r)).obj M ⟶
      (modulePullback B S hS (reprSpaceMap B S hS p)).obj
        ((modulePullback B S hS (reprSpaceMap B S hS g)).obj M))
    (hτM : ∀ x, reprChartSection B S hS p _ (reprChartSection B S hS g M x) =
      τM.val.app (op (idEtaleChart B S hS P)) (reprChartSection B S hS r M x))
    (τN : (modulePullback B S hS (reprSpaceMap B S hS r)).obj N ⟶
      (modulePullback B S hS (reprSpaceMap B S hS p)).obj
        ((modulePullback B S hS (reprSpaceMap B S hS g)).obj N))
    (hτN : ∀ x, reprChartSection B S hS p _ (reprChartSection B S hS g N x) =
      τN.val.app (op (idEtaleChart B S hS P)) (reprChartSection B S hS r N x))
    (τNi : (modulePullback B S hS (reprSpaceMap B S hS p)).obj
        ((modulePullback B S hS (reprSpaceMap B S hS g)).obj N) ⟶
      (modulePullback B S hS (reprSpaceMap B S hS r)).obj N)
    (hi : ∀ y, τNi.val.app (op (idEtaleChart B S hS P))
      (τN.val.app (op (idEtaleChart B S hS P)) y) = y)
    (m : reprSec B S hS M)
    (ξ : letI := reprAlgebra B S hS g
      TensorProduct (reprRing B S hS T) (reprRing B S hS U) (reprSec B S hS N))
    (hξ : reprBaseChange B S hS g N ξ =
      α.val.app (op (idEtaleChart B S hS U)) (reprChartSection B S hS g M m)) :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS r
    reprBaseChange B S hS r N
        (LinearMap.rTensor (reprSec B S hS N) (reprRestrictLinear B S hS p g hr) ξ) =
      (τM ≫ (modulePullback B S hS (reprSpaceMap B S hS p)).map α ≫ τNi).val.app
        (op (idEtaleChart B S hS P)) (reprChartSection B S hS r M m) := by
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS r
  have h1 := reprChartSection_reprBaseChange B S hS p g hr N τN hτN ξ
  refine (hi _).symm.trans ?_
  refine (congrArg (fun z => τNi.val.app (op (idEtaleChart B S hS P)) z) h1.symm).trans ?_
  refine (congrArg (fun z => τNi.val.app (op (idEtaleChart B S hS P))
    (reprChartSection B S hS p _ z)) hξ).trans ?_
  refine (congrArg (fun z => τNi.val.app (op (idEtaleChart B S hS P)) z)
    (reprChartSection_map B S hS p α _).symm).trans ?_
  exact congrArg (fun z => τNi.val.app (op (idEtaleChart B S hS P))
    (((modulePullback B S hS (reprSpaceMap B S hS p)).map α).val.app
      (op (idEtaleChart B S hS P)) z)) (hτM m)

/-- The family of rings of a finite family of represented morphisms into `U`, with their
algebra structures. -/
abbrev reprFamilyAlgebra {U : BigFppfOver B S hS} {K : Type*} {T : K → BigFppfOver B S hS}
    (f : ∀ k, T k ⟶ U) (k : K) : Algebra (reprRing B S hS U) (reprRing B S hS (T k)) :=
  reprAlgebra B S hS (f k)


/-- **A linear map of the sections over an affine terminal chart of a quasi-coherent module is
the value of a morphism of modules.** -/
theorem exists_hom_of_linearMap_of_isTerminal {X : AlgebraicSpaces B S hS}
    {t : SmallEtale B S hS X.1} (ht : IsTerminal t)
    (haff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj t))
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite) (P : M.Presentation)
    (φ : M.val.obj (op t) →ₗ[chartRing B S hS X.1 X.2 t] N.val.obj (op t)) :
    ∃ u : M ⟶ N, ∀ x, u.val.app (op t) x = φ x := by
  let gs : N.sections ≃ N.val.obj (op t) :=
    Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N ht
  let v : SheafOfModules.free (R := structureRingSheaf B S hS X) P.generators.I ⟶ N :=
    N.freeHomEquiv.symm fun i => gs.symm (φ ((P.generators.s i).val (op t)))
  have hL : (v.val.app (op t)).hom ∘ₗ
        (Stacks.Sites.freeSectionsMap (R := structureRingSheaf B S hS X) P.generators.I
          (op t)).hom =
      φ ∘ₗ (P.generators.π.val.app (op t)).hom ∘ₗ
        (Stacks.Sites.freeSectionsMap (R := structureRingSheaf B S hS X) P.generators.I
          (op t)).hom := by
    refine Finsupp.lhom_ext fun i x => ?_
    change (v.val.app (op t)).hom ((Stacks.Sites.freeSectionsMap
        (R := structureRingSheaf B S hS X) P.generators.I (op t)).hom (Finsupp.single i x)) =
      φ ((P.generators.π.val.app (op t)).hom ((Stacks.Sites.freeSectionsMap
        (R := structureRingSheaf B S hS X) P.generators.I (op t)).hom (Finsupp.single i x)))
    rw [Stacks.Sites.freeSectionsMap_single]
    have hx : ((SheafOfModules.ιFree (R := structureRingSheaf B S hS X) i).val.app (op t)).hom x =
        x • ((SheafOfModules.ιFree (R := structureRingSheaf B S hS X) i).val.app (op t)).hom
          (1 : chartRing B S hS X.1 X.2 t) := by
      refine Eq.trans ?_ (((SheafOfModules.ιFree (R := structureRingSheaf B S hS X) i).val.app
        (op t)).hom.map_smul x _)
      exact congrArg _ (mul_one x).symm
    have e1 : (v.val.app (op t)).hom
        (((SheafOfModules.ιFree (R := structureRingSheaf B S hS X) i).val.app (op t)).hom
          (1 : chartRing B S hS X.1 X.2 t)) = (N.freeHomEquiv v i).val (op t) := rfl
    have e2 : (P.generators.π.val.app (op t)).hom
        (((SheafOfModules.ιFree (R := structureRingSheaf B S hS X) i).val.app (op t)).hom
          (1 : chartRing B S hS X.1 X.2 t)) =
        (M.freeHomEquiv P.generators.π i).val (op t) := rfl
    rw [hx]
    refine ((v.val.app (op t)).hom.map_smul x _).trans ?_
    refine Eq.trans ?_ (congrArg φ ((P.generators.π.val.app (op t)).hom.map_smul x _)).symm
    refine Eq.trans ?_ (φ.map_smul x _).symm
    refine congrArg (fun z => x • z) ?_
    rw [e1, e2, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact gs.apply_symm_apply _
  have hv : ∀ y, (v.val.app (op t)).hom y = φ ((P.generators.π.val.app (op t)).hom y) := by
    intro y
    obtain ⟨z, rfl⟩ := (bijective_freeSectionsMap_of_isAffine B S hS X.1 X.2
      P.generators.I t haff).2 y
    exact congrArg (fun L => L z) hL
  have hk : ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) ≫ v = 0 := by
    refine (Category.assoc _ _ _).trans ?_
    refine N.freeHomEquiv.injective (funext fun j =>
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N ht).injective ?_)
    have e0 : (P.relations.π.val.app (op t)).hom
        ((SheafOfModules.freeSection (R := structureRingSheaf B S hS X) j).val (op t)) =
        (P.relations.s j).val (op t) :=
      congrArg (fun σ => σ.val (op t))
        (congrFun ((kernel P.generators.π).freeHomEquiv.apply_symm_apply P.relations.s) j)
    have h0 : (P.generators.π.val.app (op t)).hom (((kernel.ι P.generators.π).val.app (op t)).hom
        ((P.relations.s j).val (op t))) = 0 := by
      have := congrArg (fun m : kernel P.generators.π ⟶ M => (m.val.app (op t)).hom
        ((P.relations.s j).val (op t))) (kernel.condition P.generators.π)
      exact this
    have h1 : (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N ht)
        (N.freeHomEquiv (P.relations.π ≫ kernel.ι P.generators.π ≫ v) j) =
        (v.val.app (op t)).hom (((kernel.ι P.generators.π).val.app (op t)).hom
          ((P.relations.π.val.app (op t)).hom
            ((SheafOfModules.freeSection (R := structureRingSheaf B S hS X) j).val (op t)))) :=
      rfl
    have h2 : (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N ht)
        (N.freeHomEquiv (0 : SheafOfModules.free _ ⟶ N) j) = 0 := rfl
    refine h1.trans (Eq.trans ?_ h2.symm)
    refine (congrArg (fun z => (v.val.app (op t)).hom (((kernel.ι P.generators.π).val.app
      (op t)).hom z)) e0).trans ?_
    refine (hv _).trans ?_
    exact (congrArg φ h0).trans (map_zero φ)
  let hcok := P.isColimit
  obtain ⟨w, hu⟩ : ∃ w : M ⟶ N, P.generators.π ≫ w = v :=
    ⟨hcok.desc (CokernelCofork.ofπ v hk), hcok.fac (CokernelCofork.ofπ v hk)
      WalkingParallelPair.one⟩
  refine ⟨w, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := surjective_generators_app_of_isAffine B S hS X.1 X.2 hM P t haff x
  refine Eq.trans ?_ (hv y)
  exact congrArg (fun m : SheafOfModules.free _ ⟶ N => (m.val.app (op t)).hom y) hu

/-- An isomorphism of modules, read on sections: its inverse undoes it. -/
theorem iso_inv_val_app_hom_val_app {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N) (t : SmallEtale B S hS X.1)
    (y : M.val.obj (op t)) : e.inv.val.app (op t) (e.hom.val.app (op t) y) = y :=
  congrArg (fun φ : M ⟶ M => φ.val.app (op t) y) e.hom_inv_id

/-- Conjugation by the composition comparison along a triangle of represented morphisms. -/
theorem conjHom_eq_reprTriangle {T'' T' T : BigFppfOver B S hS}
    (k : T'' ⟶ T') (g : T' ⟶ T) {l : T'' ⟶ T} (hl : k ≫ g = l)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (α : (modulePullback B S hS (reprSpaceMap B S hS g)).obj M ⟶
      (modulePullback B S hS (reprSpaceMap B S hS g)).obj N) :
    Functor.conjHom (modulePullbackTriangle B S hS (reprSpaceMap_comp_eq B S hS k g hl)) α =
      (reprTriangle B S hS k g hl M).hom ≫ (modulePullback B S hS (reprSpaceMap B S hS k)).map α ≫
        (reprTriangle B S hS k g hl N).inv := rfl

section Affine

variable {T : BigFppfOver B S hS}

/-- **A quasi-coherent module on an affine represented algebraic space has a global
presentation.** -/
theorem nonempty_presentation_of_isAffine (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (hM : M.IsQuasicoherentOnSite) :
    Nonempty M.Presentation := by
  obtain ⟨P⟩ := nonempty_presentation_modulePullback_chartToSpace_of_isAffine B S hS
    (representedAlgebraicSpace B S hS T) M hM (idEtaleChart B S hS T) hT
  exact ⟨SheafOfModules.Presentation.ofIsIso
    (((modulePushforwardCoherence B S hS).modulePullbackIdIso
      (representedAlgebraicSpace B S hS T)).app M).hom P⟩

/-- A section of a module on a represented algebraic space is determined by its value over the
identity chart. -/
theorem reprSections_ext {N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} {σ τ : N.sections}
    (h : σ.val (op (idEtaleChart B S hS T)) = τ.val (op (idEtaleChart B S hS T))) : σ = τ :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N
    (isTerminalIdEtaleChart B S hS T)).injective h

/-- Two morphisms out of a free module on a represented algebraic space agreeing on the values
of the tautological sections over the identity chart are equal. -/
theorem reprFree_hom_ext {I : Type u}
    {N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    {f g : SheafOfModules.free
      (R := structureRingSheaf B S hS (representedAlgebraicSpace B S hS T)) I ⟶ N}
    (h : ∀ i, f.val.app (op (idEtaleChart B S hS T))
        ((SheafOfModules.freeSection (R := structureRingSheaf B S hS
          (representedAlgebraicSpace B S hS T)) i).val (op (idEtaleChart B S hS T))) =
      g.val.app (op (idEtaleChart B S hS T))
        ((SheafOfModules.freeSection (R := structureRingSheaf B S hS
          (representedAlgebraicSpace B S hS T)) i).val (op (idEtaleChart B S hS T)))) : f = g :=
  N.freeHomEquiv.injective (funext fun i => reprSections_ext B S hS (h i))

/-- **A morphism of modules out of a quasi-coherent module on an affine represented algebraic
space is determined by its value over the identity chart.** -/
theorem reprHom_ext_of_isAffine (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite) {u v : M ⟶ N}
    (h : ∀ x, u.val.app (op (idEtaleChart B S hS T)) x = v.val.app (op (idEtaleChart B S hS T)) x) :
    u = v := by
  obtain ⟨P⟩ := nonempty_presentation_of_isAffine B S hS hT M hM
  refine (cancel_epi P.generators.π).1 (reprFree_hom_ext B S hS fun i => ?_)
  exact h _

/-- **A morphism out of the inverse image of a quasi-coherent module along a morphism of
affine represented algebraic spaces is determined by its values on the chart sections.** -/
theorem reprPullback_hom_ext {T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite)
    {N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T').1
      (representedAlgebraicSpace B S hS T').2}
    {v w : (modulePullback B S hS (reprSpaceMap B S hS g)).obj M ⟶ N}
    (h : ∀ m, v.val.app (op (idEtaleChart B S hS T')) (reprChartSection B S hS g M m) =
      w.val.app (op (idEtaleChart B S hS T')) (reprChartSection B S hS g M m)) : v = w := by
  let := reprAlgebra B S hS g
  refine reprHom_ext_of_isAffine B S hS hT'
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM) fun x => ?_
  obtain ⟨ζ, rfl⟩ := (bijective_reprBaseChange B S hS g hT' hT M hM).2 x
  induction ζ using TensorProduct.inductionOn with
  | tmul b m => rw [reprBaseChange_tmul, map_smul, map_smul, h m]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Fpqc descent of morphisms of quasi-coherent modules along a finite family of affine
represented morphisms into an affine represented algebraic space.**  The overlaps are given by
affine objects `P j k` with projections whose rings are pushouts. -/
theorem exists_hom_of_reprFamily (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {ι : Type*} [Finite ι] {U : ι → BigFppfOver B S hS}
    (hU : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (U j))) (g : ∀ j, U j ⟶ T)
    (hff : letI := reprFamilyAlgebra B S hS g
      Module.FaithfullyFlat (reprRing B S hS T) (∀ j, reprRing B S hS (U j)))
    (P : ι → ι → BigFppfOver B S hS)
    (hP : ∀ j k, IsAffine ((BigFppfOver.toScheme B S hS).obj (P j k)))
    (p : ∀ j k, P j k ⟶ U j) (q : ∀ j k, P j k ⟶ U k)
    (hpq : ∀ j k, q j k ≫ g k = p j k ≫ g j)
    (hpush : ∀ j k, letI := reprAlgebra B S hS (g j); letI := reprAlgebra B S hS (g k)
      letI := reprAlgebra B S hS (p j k ≫ g j)
      Function.Bijective (Algebra.TensorProduct.productMap
        (reprRestrictAlgHom B S hS (p j k) (g j) rfl)
        (reprRestrictAlgHom B S hS (q j k) (g k) (hpq j k))))
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (α : ∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j))).obj M ⟶
      (modulePullback B S hS (reprSpaceMap B S hS (g j))).obj N)
    (hα : ∀ j k, Functor.conjHom (modulePullbackTriangle B S hS
        (reprSpaceMap_comp_eq B S hS (p j k) (g j) rfl)) (α j) =
      Functor.conjHom (modulePullbackTriangle B S hS
        (reprSpaceMap_comp_eq B S hS (q j k) (g k) (hpq j k))) (α k)) :
    ∃ β : M ⟶ N, ∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j))).map β = α j := by
  let := reprFamilyAlgebra B S hS g
  let eN : ∀ j, _ := fun j => LinearEquiv.ofBijective (reprBaseChange B S hS (g j) N)
    (bijective_reprBaseChange B S hS (g j) (hU j) hT N hN)
  let L : ∀ j, reprSec B S hS M →ₗ[reprRing B S hS T]
      TensorProduct (reprRing B S hS T) (reprRing B S hS (U j)) (reprSec B S hS N) := fun j =>
    { toFun := fun m => (eN j).symm ((α j).val.app (op (idEtaleChart B S hS (U j)))
        (reprChartSection B S hS (g j) M m))
      map_add' := fun a b => by
        rw [reprChartSection_add, ((α j).val.app (op (idEtaleChart B S hS (U j)))).hom.map_add,
          map_add]
      map_smul' := fun a b => by
        rw [reprChartSection_smul, ((α j).val.app (op (idEtaleChart B S hS (U j)))).hom.map_smul,
          LinearEquiv.map_smul, RingHom.id_apply]
        exact (algebraMap_smul (reprRing B S hS (U j)) a _).symm }
  have hL : ∀ j m, reprBaseChange B S hS (g j) N (L j m) =
      (α j).val.app (op (idEtaleChart B S hS (U j))) (reprChartSection B S hS (g j) M m) :=
    fun j m => (eN j).apply_symm_apply _
  have hov : ∀ j k m,
      let := reprAlgebra B S hS (p j k ≫ g j)
      LinearMap.rTensor (reprSec B S hS N) (reprRestrictLinear B S hS (p j k) (g j) rfl) (L j m) =
        LinearMap.rTensor (reprSec B S hS N) (reprRestrictLinear B S hS (q j k) (g k) (hpq j k))
          (L k m) := by
    intro j k m
    let := reprAlgebra B S hS (p j k ≫ g j)
    refine (bijective_reprBaseChange B S hS (p j k ≫ g j) (hP j k) hT N hN).1 ?_
    have key : ∀ (i : ι) (e : P j k ⟶ U i) (hr : e ≫ g i = p j k ≫ g j),
        reprBaseChange B S hS (p j k ≫ g j) N
          (LinearMap.rTensor (reprSec B S hS N) (reprRestrictLinear B S hS e (g i) hr) (L i m)) =
        ((reprTriangle B S hS e (g i) hr M).hom ≫
          (modulePullback B S hS (reprSpaceMap B S hS e)).map (α i) ≫
          (reprTriangle B S hS e (g i) hr N).inv).val.app
          (op (idEtaleChart B S hS (P j k))) (reprChartSection B S hS _ M m) := fun i e hr =>
      reprBaseChange_rTensor_restrict B S hS e (g i) hr (α i)
        (reprTriangle B S hS e (g i) hr M).hom (reprChartSection_triangle B S hS _ _ hr M)
        (reprTriangle B S hS e (g i) hr N).hom (reprChartSection_triangle B S hS _ _ hr N)
        (reprTriangle B S hS e (g i) hr N).inv
        (iso_inv_val_app_hom_val_app B S hS (reprTriangle B S hS e (g i) hr N) _)
        m (L i m) (hL i m)
    refine (key j (p j k) rfl).trans (Eq.trans ?_ (key k (q j k) (hpq j k)).symm)
    rw [← conjHom_eq_reprTriangle B S hS (p j k) (g j) rfl,
      ← conjHom_eq_reprTriangle B S hS (q j k) (g k) (hpq j k), hα j k]
  let : ∀ j k, Algebra (reprRing B S hS T) (reprRing B S hS (P j k)) := fun j k =>
    reprAlgebra B S hS (p j k ≫ g j)
  obtain ⟨f, hf⟩ := Stacks.Descent.exists_linearMap_eq_family_of_pushout
    (fun j => reprRing B S hS (U j)) (fun j k => reprRing B S hS (P j k))
    (fun j k => reprRestrictLinear B S hS (p j k) (g j) rfl)
    (fun j k => reprRestrictLinear B S hS (q j k) (g k) (hpq j k))
    (fun j k => reprRestrictAlgHom B S hS (p j k) (g j) rfl)
    (fun j k => reprRestrictAlgHom B S hS (q j k) (g k) (hpq j k))
    (fun _ _ => rfl) (fun _ _ => rfl) hpush L hov
  obtain ⟨Pr⟩ := nonempty_presentation_of_isAffine B S hS hT M hM
  obtain ⟨β, hβ⟩ := exists_hom_of_linearMap_of_isTerminal B S hS
    (X := representedAlgebraicSpace B S hS T) (t := idEtaleChart B S hS T)
    (isTerminalIdEtaleChart B S hS T) hT hM Pr f
  refine ⟨β, fun j => reprPullback_hom_ext B S hS (g j) (hU j) hT hM fun m => ?_⟩
  refine (reprChartSection_map B S hS (g j) β m).trans ?_
  refine Eq.trans ?_ (hL j m)
  rw [hf j m, hβ m, reprBaseChange_tmul, one_smul]

/-- Pullback of regular functions along a flat morphism of affine represented schemes is flat. -/
theorem flat_reprRestrict {T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hg : Flat ((BigFppfOver.toScheme B S hS).map g)) :
    (reprRestrict B S hS g).Flat := by
  have := hT
  have := hT'
  have h := HasRingHomProperty.appTop @Flat ((BigFppfOver.toScheme B S hS).map g) hg
  exact h

/-- **The ring of a finite flat jointly surjective family of affine schemes over an affine
scheme is faithfully flat**, through the global sections. -/
theorem faithfullyFlat_reprFamily (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {ι : Type*} [Finite ι] {U : ι → BigFppfOver B S hS}
    (hU : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (U j))) (g : ∀ j, U j ⟶ T)
    (hflat : ∀ j, Flat ((BigFppfOver.toScheme B S hS).map (g j)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj T, ∃ j y,
      ((BigFppfOver.toScheme B S hS).map (g j)).base y = x) :
    letI := reprFamilyAlgebra B S hS g
    Module.FaithfullyFlat (reprRing B S hS T) (∀ j, reprRing B S hS (U j)) := by
  let := reprFamilyAlgebra B S hS g
  have := hT
  have hpi := RingHom.FaithfullyFlat.pi (fun j => reprRestrict B S hS (g j))
    (fun j => flat_reprRestrict B S hS (g j) (hU j) hT (hflat j)) (fun p => by
      obtain ⟨j, y, hy⟩ := hsurj (((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv.base p)
      have := hU j
      refine ⟨j, ((BigFppfOver.toScheme B S hS).obj (U j)).isoSpec.hom.base y, ?_⟩
      have h1 := congrArg (fun φ => φ.base y)
        (Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map (g j)))
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
      rw [hy] at h1
      have h2 : (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom.base
          (((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv.base p)) = p :=
        congrArg (fun φ => φ.base p)
          ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv_hom_id
      exact h1.trans h2)
  exact (RingHom.faithfullyFlat_algebraMap_iff).1 hpi

/-- The fibre product of two affine objects over an affine object of the big fppf category is
affine. -/
theorem isAffine_pullback_bigFppfOver {U V : BigFppfOver B S hS} (g : U ⟶ T) (g' : V ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback g g')) := by
  have := hT; have := hU; have := hV
  exact IsAffine.of_isPullback
    ((IsPullback.of_hasPullback g g').map (BigFppfOver.toScheme B S hS))

/-- **The ring of the fibre product of two affine objects over an affine object is the tensor
product of their rings**, through the canonical map. -/
theorem bijective_productMap_reprRestrict {U V : BigFppfOver B S hS} (g : U ⟶ T) (g' : V ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    letI := reprAlgebra B S hS g; letI := reprAlgebra B S hS g'
    letI := reprAlgebra B S hS (pullback.fst g g' ≫ g)
    Function.Bijective (Algebra.TensorProduct.productMap
      (reprRestrictAlgHom B S hS (pullback.fst g g') g rfl)
      (reprRestrictAlgHom B S hS (pullback.snd g g') g' pullback.condition.symm)) := by
  let := reprAlgebra B S hS g; let := reprAlgebra B S hS g'
  let := reprAlgebra B S hS (pullback.fst g g' ≫ g)
  have := hT; have := hU; have := hV
  have h := isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback g g').map (BigFppfOver.toScheme B S hS))
  exact Stacks.Descent.bijective_productMap_of_isPushout _ _ h

end Affine

end AlgebraicGeometry.Space

end
