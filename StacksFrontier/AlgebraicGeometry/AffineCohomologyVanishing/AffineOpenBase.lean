module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
import StacksCore.Tactic.StacksAttribute

/-!
# The degeneration of [Stacks, Tag 01XK] over an affine open of the base

`Stacks.Cohomology.AffineBase.preservesLeftHomology_pushforward_injectiveResolution` is the
pointwise hypothesis Grothendieck's comparison `R^n(Γ ∘ f_*) ≅ Γ ∘ R^n f_*` carries, inhabited
for **global** sections of the base, and it asks `IsAffine` of the base itself. That is more than
the mathematics needs: the three inputs it is assembled from — [Stacks, Tag 01EX] part (2) for
the terms, [Stacks, Tag 01XJ] for the homology objects and [Stacks, Tag 01XB] for the vanishing —
are each stated at an **arbitrary open** of the base, and the affineness is used only through
[Stacks, Tag 01XB], which asks it of that open.

So the same statement holds for sections over any affine open `V ⊆ S`, with **nothing assumed of
`S`**. That is what this file supplies, at the
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` spelling the consumers of the
comparison use.

## Main results

* `rightAcyclic_sectionsOverOpen_of_isAffineOpen`: **[Stacks, Tag 01XB] as acyclicity of
  module-valued sections over an affine open.** For an affine open `V` of a scheme `S` and a
  quasi-coherent `𝒪_S`-module `F`, the functor `Γ(V, -)` is right acyclic at `F`. Nothing is
  assumed of `S`; this is `rightAcyclic_moduleGlobalSections` with the open kept general, both
  of whose inputs already were.
* `preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen`: **the degeneration
  over an affine open.** For a quasi-compact quasi-separated `f : X ⟶ S`, an affine open
  `V ⊆ S`, a quasi-coherent `F` on `X` and a degree `n`, sections over `V` preserve the left
  homology of the degree-`n` short complex of `f_*` of the chosen injective resolution of `F`.
  Again nothing is assumed of `S`.

## Implementation notes

The affineness of `V` is taken as `AlgebraicGeometry.IsAffineOpen`, an explicit argument, rather
than as `[IsAffine (V : Scheme)]`: that is the form [Stacks, Tag 01XB] is stated at here, and the
two are interchangeable at the consumer.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.AffineBase

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **[Stacks, Tag 01XB] read as acyclicity of module-valued sections over an affine open.** For
an affine open `V` of a scheme `S` and a quasi-coherent `𝒪_S`-module `F`, the positive-degree
right derived functors of `Γ(V, -)` vanish at `F`.

This is `rightAcyclic_moduleGlobalSections` with the open left general — both of its inputs,
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` and
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, already are — so **nothing is assumed of
`S`**, only of `V`. -/
public theorem rightAcyclic_sectionsOverOpen_of_isAffineOpen (S : AlgebraicGeometry.Scheme.{u})
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (F : S.Modules) [F.IsQuasicoherent] :
    (sectionsOverOpen S.toSheafedSpace V).rightAcyclic F := by
  refine (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
    (sectionsOverOpen S.toSheafedSpace V) F).2 fun n hn => ?_
  refine module_isZero_of_forget₂_isZero _ (IsZero.of_iso ?_
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      S.ringCatSheaf V n).app F))
  exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F V hV n hn

/-- **The degeneration of [Stacks, Tag 01XK] over an affine open of the base.** For a
quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S`, an affine open `V ⊆ S`, a
quasi-coherent `𝒪_X`-module `F` and a degree `n`, sections over `V` preserve the left homology of
the degree-`n` short complex of the image under `f_*` of the chosen injective resolution of `F`.

This is Grothendieck's pointwise hypothesis at the pair `(f_*, Γ(V, -))`, and it is
`preservesLeftHomology_pushforward_injectiveResolution` with the open left general: the terms of
that complex are pushforwards of injective modules, hence have acyclic sections over **any** open
by [Stacks, Tag 01EX] part (2); its homology objects are the higher direct images, quasi-coherent
by [Stacks, Tag 01XJ], hence acyclic over an **affine** open by [Stacks, Tag 01XB].

So **nothing is assumed of `S`** — in particular `S` need not be affine, only `V` — which is what
makes the comparison available over an affine open of an arbitrary base. -/
public theorem preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiSeparated f] {V : S.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (sectionsOverOpen S.toSheafedSpace V).PreservesLeftHomologyOf
      ((((AlgebraicGeometry.Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).sc n) := by
  let P := AlgebraicGeometry.Scheme.Modules.pushforward f
  let T := sectionsOverOpen S.toSheafedSpace V
  let I := injectiveResolution F
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hX : ∀ i, T.rightAcyclic (K.X i) := fun i =>
    @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
      (asRingedSpaceHom f) (I.cocomplex.X i) (I.injective i) V
  have hH : ∀ i, T.rightAcyclic (K.homology i) := fun i =>
    T.rightAcyclic.prop_of_iso (I.isoRightDerivedObj P i)
      (rightAcyclic_sectionsOverOpen_of_isAffineOpen S hV ((P.rightDerived i).obj F))
  exact (T.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc K hX hH n).2

end Stacks.Cohomology.AffineBase

end
