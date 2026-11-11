module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.RecoveryAux.DerivedFunctorCoproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization

/-!
# Finite cohomological dimension and direct sums

Let `Λ` be a ring and let `f : X ⟶ Y` be a morphism of schemes. [Stacks, Tag 0F11] asserts
two things about a quasi-compact, quasi-separated situation of finite cohomological dimension.

1. If `cd(f) < ∞` then `Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums.
2. If `cd(X) < ∞` then `RΓ(X, -) : D(X_étale, Λ) ⟶ D(Λ)` commutes with direct sums.

The source states both for `Λ = ℤ/nℤ` with `n ≥ 1`. This file proves the abstract step of the
argument, for an arbitrary ring `Λ`, with the two inputs of the proof (finite cohomological
dimension of the module functor and its higher derived functors commuting with direct sums)
taken as hypotheses. The statements of the source, under exactly its hypotheses, are
`Stacks.EtaleCohomology.preservesColimitsOfShape_derivedDirectImage_zmod` and
`Stacks.EtaleCohomology.preservesColimitsOfShape_derivedGlobalSections_zmod` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionCoefficientsDirectSums.lean`, which apply
the two theorems here and supply both inputs from `f` (resp. `X`) quasi-compact and
quasi-separated with `cd(f) < ∞` (resp. `cd(X) < ∞`).

The argument of the source is the one of
`Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension`:
represent each `E i` by a K-injective complex with injective terms, note that the termwise
direct sum of those complexes represents the direct sum, and use the two inputs — that
`R^q f_*` vanishes above the cohomological dimension and that it commutes with direct sums —
to see that the termwise direct sum is again computed by the underived functor.

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage`
  — the abstract step of clause (1), for any unbounded right derived functor of the direct image
  `Stacks.EtaleCohomology.etaleModuleDirectImage` of sheaves of `Λ`-modules on small étale
  sites.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_of_finiteCohomologicalDimension_globalSections`
  — the abstract step of clause (2), for any unbounded right derived functor of the global sections
  `Stacks.EtaleCohomology.etaleModuleGlobalSections`.

## Implementation notes

*The input `hsums`.* That the ordinary higher direct images `R^q f_*` on the small étale site
commute with direct sums is [Stacks, Tag 09Z1] (for `f` quasi-compact and quasi-separated). It
appears here as the hypothesis `hsums`, in the shape in which the source cites it —
preservation of direct sums of every shape by every `R^q f_*` — so that this file stays
independent of the coefficients. For sheaves of `Λ`-modules, `Λ` commutative, it is proved as
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage`,
and its analogue for `H^q(X, -)` as
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections`.

*Finite cohomological dimension.* The source's hypothesis is `cd(f) < ∞`, with `cd(f)` the
cohomological dimension of [Stacks, Tag 0F0Z], and the first step of its proof is that this
makes the direct image of sheaves of `Λ`-modules a functor of finite cohomological dimension
in the sense of Derived Categories, Lemma 13.32.2 — a uniform degree above which every
`R^q f_*` vanishes on every sheaf of `Λ`-modules. That is the form `hcd` takes here, which is
also the form in which [Stacks, Tag 095U] supplies it. Note that
`AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension` is defined by the vanishing of
`R^q f_*` on *torsion abelian* sheaves; the transfer from that predicate to the category of
sheaves of `ℤ/nℤ`-modules is
`Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleDirectImage_zmod`. Stating `hcd`
on the module category keeps this file independent of it.

*Why no quasi-compactness or quasi-separatedness.* Those hypotheses of the source are what
make `cd(f)` and `cd(X)` defined, and make 09Z1 hold. The vanishing and the commuting with
direct sums are what the proof consumes, so they are taken as `hcd` and `hsums`.

*The derived functor.* The unbounded right derived functor and its comparison are left as
parameters `RF` and `α`, constrained only by
`CategoryTheory.Functor.IsRightDerivedFunctor`, and the ambient derived categories are free
`HasDerivedCategory` binders. So neither statement presupposes a construction of `Rf_*`, and
in particular neither is tied to `CategoryTheory.HasDerivedCategory.standard`.

*Direct sums.* "Commutes with direct sums" is
`CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I)`: the image of a
coproduct cocone is a coproduct cocone, which is the source's `Rf_*(⨁ E i) = ⨁ Rf_* (E i)`
read through the canonical comparison, and presupposes no existence of either coproduct. The
index type `I` ranges over the universe `max (u + 1) r` controlling the Grothendieck axioms of
the two sheaf categories.

## References

* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe z u r

namespace Stacks.EtaleCohomology

/-- **The abstract step of [Stacks, Tag 0F11] (1).** Let `Λ` be a ring and `f : X ⟶ Y` a
morphism of schemes such that the direct image of sheaves of `Λ`-modules on the small étale
sites has finite cohomological dimension, i.e. there is a degree `d` above which every higher
direct image `R^q f_*` vanishes on every sheaf of `Λ`-modules. Then any unbounded right
derived functor `Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums.

The hypothesis `hcd` is the source's `cd(f) < ∞`, in the shape its proof uses it and in which
[Stacks, Tag 095U] supplies it. The hypothesis `hsums` is [Stacks, Tag 09Z1], that each
`R^q f_*` commutes with direct sums. Both are supplied from the hypotheses of the source in
`Stacks.EtaleCohomology.preservesColimitsOfShape_derivedDirectImage_zmod`, the statement of
Tag 0F11 (1). -/
theorem preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage
    (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{z} (EtaleModules.{u, r} Λ X)]
    [HasDerivedCategory.{z} (EtaleModules.{u, r} Λ Y)]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj F))
    (hsums : ∀ (q : ℕ) (I : Type (max (u + 1) r)),
      PreservesColimitsOfShape (Discrete I)
        ((etaleModuleDirectImage.{u, r} Λ f).rightDerived q))
    (RF : DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ Y))
    (α : (etaleModuleDirectImage.{u, r} Λ f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))]
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension
    _ _ (etaleModuleDirectImage.{u, r} Λ f) hcd.choose hcd.choose_spec hsums RF α I

/-- **The abstract step of [Stacks, Tag 0F11] (2).** Let `Λ` be a ring and `X` a scheme such
that global sections of sheaves of `Λ`-modules on the small étale site of `X` has finite
cohomological dimension, i.e. there is a degree `d` above which every `H^q(X, -)` vanishes on
every sheaf of `Λ`-modules.
Then any unbounded right derived functor `RΓ(X, -) : D(X_étale, Λ) ⟶ D(Λ)` commutes with direct
sums.

The hypothesis `hcd` is the source's `cd(X) < ∞`, and `hsums` is [Stacks, Tag 09Z1] read on the
structure morphism of `X`, that each `H^q(X, -)` commutes with direct sums. Both are supplied
from the hypotheses of the source in
`Stacks.EtaleCohomology.preservesColimitsOfShape_derivedGlobalSections_zmod`, the statement of
Tag 0F11 (2). -/
theorem preservesColimitsOfShape_of_finiteCohomologicalDimension_globalSections
    (Λ : Type r) [Ring Λ] (X : Scheme.{u})
    [HasDerivedCategory.{z} (EtaleModules.{u, r} Λ X)]
    [HasDerivedCategory.{z} (ModuleCat.{max (u + 1) r} Λ)]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F))
    (hsums : ∀ (q : ℕ) (I : Type (max (u + 1) r)),
      PreservesColimitsOfShape (Discrete I)
        ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q))
    (RF : DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) r} Λ))
    (α : (etaleModuleGlobalSections.{u, r} Λ X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))]
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension
    _ _ (etaleModuleGlobalSections.{u, r} Λ X) hcd.choose hcd.choose_spec hsums RF α I

end Stacks.EtaleCohomology

end
