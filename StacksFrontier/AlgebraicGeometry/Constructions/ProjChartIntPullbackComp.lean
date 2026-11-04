module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackMul
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cocycle law for the pullback comparison of Tag 01CU's integer tensor powers

Let `j : Y' ⟶ Y` and `j' : Y'' ⟶ Y'` be morphisms of schemes and `L` an invertible
`𝒪_Y`-module. `Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso` is the comparison
`j^*(L^{⊗ n}) ≅ (j^*L)^{⊗ n}` of [Stacks, Tag 01CU]'s integer tensor powers under pullback, at
the `AlgebraicGeometry.Scheme.Modules.pullback` spelling of the inverse image. This file states
and proves its **cocycle law**: comparing along `j` and then along `j'`, and transporting the
result along the comparison `j'^*j^*L ≅ (j' ≫ j)^*L` of the composition law for pullback, is
contracting the iterated pullback and comparing along `j' ≫ j`.

## The mathematics is already in the library

Nothing here is new content. The induction was done in
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition.pieceIso_comp` — a two-sided
`Int.induction_on` out of degree zero, whose base case is
`Stacks.PullbackTensorCoherence.pullbackUnitComparison_comp` and whose step is the compatibility
of the composition law with the cotensorator — and read through
`…RelativeProjQcohSheaf.UnionFunctor.pieceIso_hom_eq_laurentPullback` it is
`…RelativeProjQcohSheaf.UnionFunctor.laurentPullback_comp`. Uniqueness of coherence data
(`Stacks.TensorPowerCoherence.mulIso_eq`) does **not** apply: it identifies two multiplications
on one family of powers, whereas a cocycle law compares two *morphisms* between different
families, and the comparison is not coherence data for anything.

What this file supplies is the **spelling bridge**. Three facts make it a one-liner, and all
three hold by `rfl`:

* `(laurent L).piece n` is `Stacks.AmpleProjectiveImmersion.tensorPowerModule Y L n`;
* `…RelativeProjQcohSheaf.laurentPullback j L n` is `(intPullIso j L n).hom`, both being
  `Stacks.TensorPowerPullback.pullbackIntPowIso j.toLRSHom.toShHom L n`;
* `(AlgebraicGeometry.Scheme.Modules.pullbackComp j' j).hom.app M` is
  `(…LaurentComposition.compCmp j' j M).hom`. The two isomorphisms are **not** `rfl`-equal as
  bundled isomorphisms — that is
  `Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp`, which needs `Iso.ext` — but their
  components are, and only the components are used here.

## The transport on the right-hand side

The right-hand side ends in `…LaurentCongr.congrIso`, the degreewise transport of an isomorphism
of invertible modules, rather than in
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` (equivalently
`Stacks.TwistTensor.tensorPowerModuleCongr`). The two are not known to agree — see the module
docstring of `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentCongr.lean` — and
`congrIso` is the one that carries a successor law, hence the one the induction behind
`laurentPullback_comp` reaches.

Its argument must be written at the **nested** `Scheme.Modules.pullback` spelling and not as the
value of the composite functor `pullback j ⋙ pullback j'`: instance search finds the
invertibility of an iterated pullback only when it can see the two inverse images, so
`(Scheme.Modules.pullbackComp j' j).app L` is re-ascribed as `compPullIso` below.

## Main results

* `…ProjChartIntPullbackComp.compPullIso` — the comparison `j'^*j^*L ≅ (j' ≫ j)^*L`, ascribed at
  the nested spelling.
* `…ProjChartIntPullbackComp.intPullIso_comp` — **the cocycle law**.
* `…ProjChartIntPullbackComp.intPullIso_comp_inv` — the same law solved for the comparison along
  the composite, which is the direction a nested compatibility consumes.
* `…ProjChartIntPullbackComp.intPullIsoAt` and `…ProjChartIntPullbackComp.intPullIso_nested` —
  **the shape a nested compatibility consumes**: the comparison along a morphism `jj` that an
  equation `j' ≫ j = jj` presents as a composite, with the identification of the two readings of
  the inverse image supplied as an argument together with its defining equation rather than
  chosen here. This is the scheme-level counterpart of
  `…RelativeProjQcohSheaf.laurentPullbackCongrIso_pullback`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurentPullback_comp)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition (compCmp)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartIntPullbackComp

attribute [local instance] Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.stacksInvertible

variable {Y Y' Y'' : Scheme.{u}} (j : Y' ⟶ Y) (j' : Y'' ⟶ Y') (L : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The comparison `j'^*j^*L ≅ (j' ≫ j)^*L` of the composition law for the pullback of modules**,
with its source ascribed at the iterated `AlgebraicGeometry.Scheme.Modules.pullback` spelling
rather than as the value of the composite functor `pullback j ⋙ pullback j'`.

The ascription is what lets instance search see the two inverse images, and hence find the
invertibility of the iterated pullback that the degreewise transport
`…RelativeProjQcohSheaf.LaurentCongr.congrIso` is indexed by. It is the scheme-level counterpart
of `…RelativeProjQcohSheaf.LaurentComposition.compCmp`, and is that morphism: see
`compPullIso_hom`. -/
@[ega "0 4.3.6" "schemes, special case"]
def compPullIso :
    (Scheme.Modules.pullback j').obj ((Scheme.Modules.pullback j).obj L) ≅
      (Scheme.Modules.pullback (j' ≫ j)).obj L :=
  (Scheme.Modules.pullbackComp j' j).app L

omit [Ample.IsInvertibleModule Y L] in
/-- **The re-ascribed composition law is the component of the composition law.** -/
theorem compPullIso_hom :
    (compPullIso j j' L).hom = (Scheme.Modules.pullbackComp j' j).hom.app L :=
  rfl

/-- **The cocycle law for the pullback comparison of [Stacks, Tag 01CU]'s integer tensor
powers**, in every integer degree and with no hypothesis beyond invertibility: contracting the
iterated pullback of `L^{⊗ n}` and comparing along `j' ≫ j` is comparing along `j`, pulling that
back along `j'`, comparing along `j'`, and transporting the result degreewise along the
composition law at `L`.

This is `…RelativeProjQcohSheaf.UnionFunctor.laurentPullback_comp` read at the scheme spelling;
see the module docstring for the three `rfl`-identifications that make it so, and for why
uniqueness of coherence data cannot replace the induction behind it. -/
theorem intPullIso_comp (n : ℤ) :
    (Scheme.Modules.pullbackComp j' j).hom.app (tensorPowerModule Y L n) ≫
        (intPullIso (j' ≫ j) L n).hom =
      (Scheme.Modules.pullback j').map (intPullIso j L n).hom ≫
        (intPullIso j' ((Scheme.Modules.pullback j).obj L) n).hom ≫
          (congrIso (compCmp j' j L) n).hom :=
  (laurentPullback_comp j j' L n).symm

/-- **The cocycle law solved for the comparison along the composite.** This is the direction a
nested compatibility consumes: the comparison along `j' ≫ j` is the two comparisons in turn and
the degreewise transport, read back across the composition law. -/
theorem intPullIso_comp_inv (n : ℤ) :
    (intPullIso (j' ≫ j) L n).hom =
      (Scheme.Modules.pullbackComp j' j).inv.app (tensorPowerModule Y L n) ≫
        (Scheme.Modules.pullback j').map (intPullIso j L n).hom ≫
          (intPullIso j' ((Scheme.Modules.pullback j).obj L) n).hom ≫
            (congrIso (compCmp j' j L) n).hom :=
  Eq.trans
    (((Scheme.Modules.pullbackComp j' j).app (tensorPowerModule Y L n)).inv_hom_id_assoc
      ((intPullIso (j' ≫ j) L n).hom)).symm
    (congrArg (fun z => (Scheme.Modules.pullbackComp j' j).inv.app (tensorPowerModule Y L n) ≫ z)
      (intPullIso_comp j j' L n))

/-! ### The shape a nested compatibility consumes -/

/-- **The comparison of [Stacks, Tag 01CU]'s integer tensor powers along `j'`, read at a given
identification `c : j'^*M ≅ N` of the inverse image**: the comparison followed by the degreewise
transport along `c`.

This is the scheme-level counterpart of
`…RelativeProjQcohSheaf.laurentPullbackCongrIso`. The identification is an argument because a
glueing argument arrives holding one it has itself produced — over a nested pair of opens, the
identification of `(j' ≫ j)^*L` with the module that already lives over the smaller one — and
not a canonical choice made here. -/
def intPullIsoAt {M : Y'.Modules} [Stacks.Ample.IsInvertibleModule Y' M]
    {N : Y''.Modules} [Stacks.Ample.IsInvertibleModule Y'' N]
    (c : (Scheme.Modules.pullback j').obj M ≅ N) (n : ℤ) :
    (Scheme.Modules.pullback j').obj (tensorPowerModule Y' M n) ⟶ tensorPowerModule Y'' N n :=
  (intPullIso j' M n).hom ≫ (congrIso c n).hom

/-- **The cocycle law in the shape a nested compatibility consumes.** For a morphism `jj` that an
equation `j' ≫ j = jj` presents as a composite, the comparison of the integer tensor powers along
`jj` is: the congruence of the two readings of the inverse image, the contraction of the iterated
inverse image, the comparison along `j` pulled back along `j'`, and the comparison along `j'` read
at the identification `c`.

The identification `c` is an argument with its defining equation `hcc`, so that a consumer which
has already built it — a nested compatibility over a pair of opens has — need not unfold anything
at its own concrete morphisms. Substituting the two equations reduces the statement to
`intPullIso_comp_inv`: the congruence at a reflexive equality is the identity, and the
re-ascribed composition law `compPullIso` is `…LaurentComposition.compCmp` by `rfl`. -/
theorem intPullIso_nested {jj : Y'' ⟶ Y} (hc : j' ≫ j = jj)
    (c : (Scheme.Modules.pullback j').obj ((Scheme.Modules.pullback j).obj L) ≅
      (Scheme.Modules.pullback jj).obj L)
    (hcc : c = compPullIso j j' L ≪≫ (Scheme.Modules.pullbackCongr hc).app L) (n : ℤ) :
    (intPullIso jj L n).hom =
      (Scheme.Modules.pullbackCongr hc).inv.app (tensorPowerModule Y L n) ≫
        (Scheme.Modules.pullbackComp j' j).inv.app (tensorPowerModule Y L n) ≫
          (Scheme.Modules.pullback j').map (intPullIso j L n).hom ≫
            intPullIsoAt j' c n := by
  subst hc
  have hc2 : c = compPullIso j j' L := hcc.trans (Iso.trans_refl _)
  subst hc2
  exact intPullIso_comp_inv j j' L n

end Stacks.AlgebraicGeometry.ProjChartIntPullbackComp

end
