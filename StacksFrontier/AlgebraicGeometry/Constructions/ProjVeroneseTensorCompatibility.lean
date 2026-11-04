module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseAssociatedSheaf
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseTensorComparison
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The Veronese comparison and the multiplication map of Tag 01MK

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾` the Veronese subring, `M` and `N` graded
`S`-modules, and `i : Proj S ≅ Proj S'` the Veronese isomorphism. Tag 0B5J's two enumerated
assertions identify `M̃` with `i^*(M'~)` and `𝒪(nd)` with `i^*𝒪'(n)`; the unnumbered clause that
follows them asserts that those identifications are *compatible with the multiplication maps of
Tag 01MK, hence with the maps (01MO), (03GJ), (01MP), (03GK), (01MQ) and (01MR) (see proof for
precise statements*. This file states and proves the 01MK compatibility, which is what the clause
asserts — the square

```
M̃ ⊗ Ñ  ────────── 01MK on Proj S ──────────▸  (M ⊗_S N)~
  │                                                 │
(1) ⊗ (1)                                          (1)
  ▾                                                 ▾
i^*(M'~) ⊗ i^*(N'~) ── 01CD⁻¹ ──▸ i^*(M'~ ⊗ N'~) ── i^*(01MK on Proj S' ≫ c~) ──▸ i^*(((M⊗N)')~)
```

It also supplies the two arrows the square needs that the library did not have: the
associated-sheaf map of the canonical comparison `c : M' ⊗_{S'} N' ⟶ (M ⊗_S N)'`, and Tag 01CD
read in the vocabulary the 0B5J isomorphisms are written in.

## Main definitions

* `Stacks.Veronese.veroneseTensorSheafMap`: the map of associated sheaves on `Proj S⁽ᵈ⁾` induced
  by `Stacks.Veronese.veroneseTensorMap`.
* `Stacks.Veronese.veronesePullbackTensorIso`: Tag 01CD along the Veronese isomorphism, with its
  pullback written as `AlgebraicGeometry.Scheme.Modules.pullback`.
* `Stacks.Veronese.veroneseTensorSquareLeft` and
  `Stacks.Veronese.veroneseTensorSquareRight`: the two sides of the square.
* `Stacks.Veronese.VeroneseTensorCompatibility`: the square itself, as a proposition.

## Main results

* `Stacks.Veronese.veroneseTensorCompatibility`: **the square commutes** — Tag 0B5J's trailing
  clause. Its chartwise halves are `veroneseTensorSquareLeft_standardOpen`,
  `veroneseTensorSquareRight_standardOpen` and `veroneseTensorUpstairs_standardOpen`, joined for
  arbitrary sections by `veroneseTensorCompatibility_chart`.
* `Stacks.Veronese.exists_degreeZeroFraction`: every section of `M̃` over a chart is a single
  homogeneous fraction `m / f ⁿ`, which is the form Tag 01MK's chart formula consumes.
* `Stacks.Veronese.veroneseModuleAwayEquiv_degreeZeroFraction`: the Veronese identification
  `M'₍f ᵈ₎ ≅ M₍f₎` on such a fraction, in that same form on both sides.
* `Stacks.Veronese.veroneseTensorCompatibility_iff_onBasis`: the square commutes if and only if
  its two sides agree on the sections over every standard open of a positive-degree homogeneous
  element of `S`. This is the reduction of the categorical identity to the charts, which is the
  only place the square's two 0B5J isomorphisms are described.
* `Stacks.Veronese.veroneseTensorCompatibility_iff_tmul`: the square commutes if and only if its
  two sides agree on the images of pure tensors of honest sections. This is the reduction to the
  shape that the computation rules for its two upper edges are stated at.
* `Stacks.Veronese.tensorSheaf_hom_ext_onBasis_tmul`: the two reductions joined — two morphisms
  out of a tensor product of sheaves of modules agree as soon as they agree on pure tensors of
  sections over a basis of opens.
* `Stacks.Veronese.veroneseLocalizedModuleFun_veroneseTensorMap_mk` and
  `Stacks.Veronese.mk_pow_mul_add`: **the algebraic identity the source's argument reduces to**,
  namely its "since these maps agree via the identifications `M₍f₎ = M'₍f ᵈ₎`". The first says the
  Veronese identification carries the 01MK numerator `m ⊗ n` to the same pure tensor read in
  `M ⊗_S N` and the denominator `(f ᵈ)^j` to `f^(dj)`; the second says the exponent `d(j + l)`
  accumulated upstairs is the exponent `dj + dl` accumulated downstairs.
* `Stacks.Veronese.associatedModuleSheafVeroneseIso_hom_standardOpen`: assertion (1) of Tag 0B5J
  read forwards on a chart, the library having fixed it by its inverse.
* `Stacks.Veronese.veroneseTensorSheafMap_standardOpen`: the square's lower edge on a chart.
* `Stacks.Veronese.schemePullbackTensorIso_inv_toTensorSheafSection`: Tag 01CD on sections, for
  the inverse of the comparison, which is the direction the square uses.
* `Stacks.Veronese.modulesPullbackUnit_naturality`, together with
  `Stacks.Veronese.toTensorSheafSection_restrict`,
  `Stacks.Veronese.moduleSheafHom_app_restrict`, `Stacks.Veronese.presheafTensor_map_tmul`,
  `Stacks.Veronese.toTensorSheafSection_cast` and
  `Stacks.Veronese.moduleSheafIso_hom_app_inv_app`: the naturality and transport lemmas that move
  each edge of the square between an arbitrary open, a chart, and the chart's preimage.

## What is proved

`VeroneseTensorCompatibility` is proved, by `veroneseTensorCompatibility`: the square commutes.
The argument is the source's own. Both sides are morphisms out of a *sheafified* tensor product,
so they are equal as soon as they agree on pure tensors of sections over a basis of opens
(`tensorSheaf_hom_ext_onBasis_tmul`); the basis is the standard opens of positive-degree
homogeneous elements, which is where the square's two 0B5J isomorphisms are described; and over
`D₊(f) = i⁻¹D₊(f ᵈ)` both sides send the pure tensor of `m / f^(pd)` and `n / f^(qd)` to the
pullback of `c(m ⊗ n) / (f ᵈ)^(p+q)` — "these maps agree via the identifications
`M₍f₎ = M'₍f ᵈ₎`". The two chart computations are `veroneseTensorSquareLeft_standardOpen` and
`veroneseTensorSquareRight_standardOpen`, and `veroneseTensorCompatibility_chart` joins them for
an arbitrary pair of sections, every section over a chart being a single homogeneous fraction by
`exists_degreeZeroFraction`.

The compatibilities the clause derives from this one, with (01MO), (03GJ), (01MP), (03GK), (01MQ)
and (01MR), are proved in `ProjVeroneseTwistMultiplication.lean`,
`ProjVeroneseTwistSheafMultiplication.lean`, `ProjVeroneseGlobalSections.lean`,
`ProjVeroneseModuleSections.lean` and `ProjVeroneseModuleTwist.lean` of this directory. The whole
tag is carried by `Stacks.Veronese.tag0B5J` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjVeroneseStatement.lean`, which holds the
library's `0B5J` attribute; nothing in this file carries one of its own.

The source's argument for the square is itself faulty: it asserts an equality
`M' ⊗_{S'} N' = (M ⊗_S N)'` of graded modules which is false, refuted by
`Stacks.Veronese.not_injective_veroneseTensorMap`: the comparison `veroneseTensorMap` is not
injective at `S = k[x, y]`, `d = 2`, `M = N = S(1)`. That is why the square here is drawn
with `veroneseTensorSheafMap` along its lower edge rather than with an identification, and why
`veroneseLocalizedModuleFun_veroneseTensorMap_mk` and `mk_pow_mul_add` are the form the
source's "these maps agree" takes: over every standard open both composites send
`m / f^(pd) ⊗ n / f^(qd)` to `c(m ⊗ n) / (f ᵈ)^(p+q)`. The erratum is in the source's proof,
not its statement.

## Implementation notes

Three definitionally equal but syntactically distinct spellings of one category meet in the
square. Tag 01MK's multiplication map `associatedModuleSheafTensorMap` and Tag 01CD's comparison
live over `Stacks.RingedSpace.structureRingSheaf`, i.e. over `SheafOfModules.{u}` of the ringed
space `(Proj 𝒮).toRingedSpace`, while 0B5J's assertions (1) and (2) are written with
`AlgebraicGeometry.Scheme.Modules.pullback`, hence over `(Proj 𝒮).Modules`, which repackages
`SheafOfModules.{u} (Proj 𝒮).ringCatSheaf`; and the tensor product itself has a name in each
spelling. The three identities hold at default transparency but are invisible to `rw` and to
instance search, so every object and every morphism here is supplied as a *free* term and
applied with `exact`: `veronesePullbackTensorIso` states Tag 01CD in the scheme spelling and
proves it by `exact` from the ringed-space term
`Stacks.PullbackTensor.pullbackTensorSheafObjIso` applied to
`(veroneseProjIso 𝒮 d hd).hom.toLRSHom.toShHom`, and `veroneseTensorSquareLeft` and
`veroneseTensorSquareRight` name the two composites so that the crossing is paid once rather
than inside each statement about them.

The chartwise reduction is `Stacks.BasisRestriction.moduleSheafHom_ext_onBasis` — two *given*
morphisms of sheaves of modules agreeing on a basis are equal — applied to the basis
`Stacks.Veronese.positiveBasicOpenSet` of standard opens of positive-degree homogeneous
elements. The existence statement `exists_moduleSheafIso_of_sectionIso_onBasis` is the wrong
tool here: it produces an isomorphism from chart data, whereas the square compares two
morphisms that are already given. The pure-tensor reduction is the other half of the same
bookkeeping: the domain of the square is a *sheafified* tensor product and
`associatedModuleSheafTensorMap` is by construction the adjoint transpose of a presheaf-level
map, so the sheafification adjunction makes the two sides equal as soon as they agree on the
image of the pointwise tensor product, where the pure tensors generate
(`Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection`).

The identity is checked on a pure tensor of sections over one chart. Every edge of the
square has a description at that shape: the two upper edges by
`associatedModuleSheafTensorMap_app_toTensorSheafSection` (in
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality`) and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection`, the right
edge by `associatedModuleSheafVeroneseIso_hom_standardOpen`, the 01CD crossing by
`schemePullbackTensorIso_inv_toTensorSheafSection`, and the lower edge by
`veroneseTensorSheafMap_standardOpen` and `modulesPullbackUnit_naturality`. One step is needed
before they compose: `associatedModuleSheafTensorMap_standardOpen` is stated for sections
presented as `ProjectiveSpectrum.Proj.degreeZeroFraction`, so arbitrary sections over the chart
are put in that form first by `exists_degreeZeroFraction`, which is
`Stacks.Veronese.mem_gradedModuleDegreeZeroLocalization_iff` read in the `degreeZeroFraction`
vocabulary.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (tensorGrading)
open scoped TensorProduct

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

universe u w

variable {S M N : Type u} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
  (𝒩 : ℤ → AddSubgroup N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]

/-- The map of associated sheaves on `Proj S⁽ᵈ⁾` induced by the canonical comparison
`Stacks.Veronese.veroneseTensorMap : M⁽ᵈ⁾ ⊗_{S⁽ᵈ⁾} N⁽ᵈ⁾ ⟶ (M ⊗_S N)⁽ᵈ⁾`. It is the lower edge of
the 01MK square, and it is there because the comparison is not an isomorphism of graded
modules. -/
public def veroneseTensorSheafMap (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (tensorGrading (S := veroneseSubring 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)) ⟶
      ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  exact associatedModuleSheafMap (veroneseGrading 𝒮 d) _ _
    (veroneseTensorMap 𝒮 𝒨 𝒩 d)
    (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d)

/-- **Tag 01CD along the Veronese isomorphism, in the scheme spelling.** Pulling back a tensor
product of sheaves of modules on `Proj S⁽ᵈ⁾` along `i` is the tensor product of the pullbacks.
It is `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` at the Veronese isomorphism, so the
pullback is spelled `AlgebraicGeometry.Scheme.Modules.pullback` — what Tag 0B5J's assertions (1)
and (2) are written with — and the comparison comes with its description on sections,
`schemePullbackTensorIso_hom_modulesPullbackUnit`, which is what the square is checked against.
The morphism is the canonical comparison `Stacks.RingedSpace.comparison` either way; the
ringed-space representative `Stacks.PullbackTensor.pullbackTensorSheafObjIso` is the same one, by
`pullbackTensorSheafObjIso_hom_eq_comparison`. -/
public def veronesePullbackTensorIso (d : ℕ) (hd : 0 < d)
    (A B : letI := veroneseGradingGradedRing 𝒮 d hd
      (_root_.AlgebraicGeometry.Proj (veroneseGrading 𝒮 d)).Modules) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(((_root_.AlgebraicGeometry.Proj (veroneseGrading 𝒮 d)).toRingedSpace)).presheaf,
            (((_root_.AlgebraicGeometry.Proj (veroneseGrading 𝒮 d)).toRingedSpace)).IsSheaf⟩).obj
            (A)).obj (B))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj A))).obj
          (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj B))) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
    (veroneseProjIso 𝒮 d hd).hom A B

/-- The upper edge of the 01MK square followed by its right edge: multiply on `Proj S`, then
transport by assertion (1) of Tag 0B5J for the graded tensor product. -/
public def veroneseTensorSquareLeft (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  exact associatedModuleSheafTensorMap 𝒮 𝒨 𝒩 ≫
    (associatedModuleSheafVeroneseIso 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd).hom

/-- The left edge of the 01MK square followed by its lower edge: transport both factors by
assertion (1) of Tag 0B5J, cross Tag 01CD, then multiply on `Proj S⁽ᵈ⁾` and apply the
associated-sheaf map of the canonical comparison. -/
public def veroneseTensorSquareRight (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  exact ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
      (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
      (X := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨,
        ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩))
      (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d)),
        (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒩 d))))
      ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom,
        (associatedModuleSheafVeroneseIso 𝒮 𝒩 d hd).hom)) ≫
    (veronesePullbackTensorIso 𝒮 d hd
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d))
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒩 d))).inv ≫
    (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (associatedModuleSheafTensorMap (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) ≫
        veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd)

/-- The standard opens `D₊(f)` of homogeneous `f` of positive degree, indexed by the pairs
`(f, e)` with `0 < e` and `f ∈ 𝒮 e`, form a basis of `Proj S`. -/
private theorem isBasis_range_basicOpen_of_pos :
    Opens.IsBasis (Set.range fun a : { p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒮 p.2 } =>
      ProjectiveSpectrum.basicOpen 𝒮 a.1.1) := by
  have heq : Set.range (fun a : { p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒮 p.2 } =>
      ProjectiveSpectrum.basicOpen 𝒮 a.1.1) = positiveBasicOpenSet (𝒮 := 𝒮) := by
    ext W
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1.1, a.1.2, a.2.1, a.2.2, rfl⟩
    · rintro ⟨f, e, he, hf, rfl⟩
      exact ⟨⟨(f, e), he, hf⟩, rfl⟩
  rw [heq]
  exact positiveBasicOpenSet_isBasis 𝒮

/-- **The compatibility of Tag 0B5J's assertion (1) with the multiplication map of Tag 01MK**,
as a proposition: the square of this file commutes. This is Tag 0B5J's trailing clause, and
`veroneseTensorCompatibility` below proves it. The tag's attribute sits on the whole-tag
carrier `Stacks.Veronese.tag0B5J`. -/
public def VeroneseTensorCompatibility (d : ℕ) (hd : 0 < d) : Prop :=
  veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd = veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd

/-- **The 01MK square commutes if and only if it commutes on the charts.** Its two sides are
morphisms of sheaves of modules on `Proj S`, so by Tag 009U they are equal as soon as they agree
on the sections over every member of a basis of opens, and the standard opens of positive-degree
homogeneous elements form such a basis. This reduces the categorical identity to the standard
opens, which is the only place the square's two 0B5J isomorphisms are described:
`associatedModuleSheafVeroneseIso_standardOpen`. -/
public theorem veroneseTensorCompatibility_iff_onBasis (d : ℕ) (hd : 0 < d) :
    VeroneseTensorCompatibility 𝒮 𝒨 𝒩 d hd ↔
      ∀ (f : S) (e : ℕ), 0 < e → f ∈ 𝒮 e →
        (veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd).val.app
            (op (ProjectiveSpectrum.basicOpen 𝒮 f)) =
          (veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd).val.app
            (op (ProjectiveSpectrum.basicOpen 𝒮 f)) := by
  refine ⟨fun h f e _ _ => congrArg
    (fun φ => φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))) h, fun h => ?_⟩
  exact Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ _
    (isBasis_range_basicOpen_of_pos 𝒮) _ _ (fun a => h a.1.1 a.1.2 a.2.1 a.2.2)

/-- **The 01MK square commutes if and only if it commutes on pure tensors of honest sections.**
The domain of the square is the *sheafified* tensor product, so by the sheafification adjunction
its two sides are equal as soon as they agree after the canonical map from the pointwise tensor
product, and the pure tensors generate that. This is the reduction that matches the computation
rules: `associatedModuleSheafTensorMap_app_toTensorSheafSection` for the upper edge and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection` for the
left edge both describe exactly these values. -/
public theorem veroneseTensorCompatibility_iff_tmul (d : ℕ) (hd : 0 < d) :
    VeroneseTensorCompatibility 𝒮 𝒨 𝒩 d hd ↔
      ∀ (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
        (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj U)
        (y : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩).val.obj U),
        ((veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd).val.app U).hom
            (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
              (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
              (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩) U
              (x ⊗ₜ[(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj U] y)) =
          ((veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd).val.app U).hom
            (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
              (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
              (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩) U
              (x ⊗ₜ[(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj U] y)) := by
  constructor
  · intro h U x y
    exact congrArg (fun φ => (φ.val.app U).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
        (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩) U
        (x ⊗ₜ[(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj U] y))) h
  · intro h
    exact Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection
      (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace _ _ h

/-! ### Reduction to pure tensors of sections over the charts -/

/-- Restriction of a pure tensor inside the *presheaf* tensor product: the restriction maps of
`presheafTensor` are the tensor product of the restriction maps of the two factors. -/
public theorem presheafTensor_map_tmul (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (_root_.structureSheafRing X))
    {U V : Opens X.carrier} (hUV : V ≤ U)
    (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    (((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))).map
        (homOfLE hUV).op).hom (x ⊗ₜ[X.presheaf.obj (op U)] y) =
      (F.val.map (homOfLE hUV).op).hom x ⊗ₜ[X.presheaf.obj (op V)]
        (G.val.map (homOfLE hUV).op).hom y :=
  ModuleCat.tensorRestrictMap_tmul (X.presheaf.map (homOfLE hUV).op).hom
    (F.val.restrictₛₗ (homOfLE hUV).op) (G.val.restrictₛₗ (homOfLE hUV).op) x y

/-- **Restricting the canonical section attached to a pure tensor.** The section of the
sheafified tensor product that `toTensorSheafSection` attaches to `x ⊗ y` restricts to the one
attached to the pure tensor of the restrictions, because `toTensorSheafSection` is a component of
the sheafification unit and hence natural. -/
public theorem toTensorSheafSection_restrict (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (_root_.structureSheafRing X))
    {U V : Opens X.carrier} (hUV : V ≤ U)
    (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (F)).obj (G))).val.map
          (homOfLE hUV).op).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op U)
          (x ⊗ₜ[X.presheaf.obj (op U)] y)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
        ((F.val.map (homOfLE hUV).op).hom x ⊗ₜ[X.presheaf.obj (op V)]
          (G.val.map (homOfLE hUV).op).hom y) :=
  (congrArg (fun φ => ModuleCat.Hom.hom φ (x ⊗ₜ[X.presheaf.obj (op U)] y))
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).naturality
          (homOfLE hUV).op)).symm.trans
    (congrArg (ModuleCat.Hom.hom
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).app (op V)))
      (presheafTensor_map_tmul X F G hUV x y))

/-- A morphism of sheaves of modules commutes with restriction, read on an element. -/
public theorem moduleSheafHom_app_restrict {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}
    {A B : SheafOfModules.{u} 𝒪} (φ : A ⟶ B)
    {U V : Opens X} (hUV : V ≤ U) (s : A.val.obj (op U)) :
    (B.val.map (homOfLE hUV).op).hom ((φ.val.app (op U)).hom s) =
      (φ.val.app (op V)).hom ((A.val.map (homOfLE hUV).op).hom s) :=
  (congrArg (fun ψ => ModuleCat.Hom.hom ψ s) (φ.val.naturality (homOfLE hUV).op)).symm

/-- **Two morphisms out of a tensor product of sheaves of modules agree as soon as they agree on
pure tensors of sections over a basis of opens.** This combines the two separate reductions —
the sheafification adjunction, which makes a morphism out of `F ⊗ G` determined by its values on
pure tensors of sections, and locality, which makes a section of the target determined by its
restrictions to a basis. It is stated with no reference to the Veronese data: the square's own
objects carry enough `letI`-bound instances that elaborating this argument at them exhausts the
heartbeat allowance of a single declaration. -/
public theorem tensorSheaf_hom_ext_onBasis_tmul
    (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    (F G T : SheafOfModules.{u} (_root_.structureSheafRing X))
    (p q : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (F)).obj (G)) ⟶ T)
    {ι : Type*} (W : ι → Opens X.carrier) (hW : Opens.IsBasis (Set.range W))
    (h : ∀ (a : ι) (x : F.val.obj (op (W a))) (y : G.val.obj (op (W a))),
      (p.val.app (op (W a))).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op (W a))
            (x ⊗ₜ[X.presheaf.obj (op (W a))] y)) =
        (q.val.app (op (W a))).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op (W a))
            (x ⊗ₜ[X.presheaf.obj (op (W a))] y))) :
    p = q := by
  refine Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection X p q ?_
  intro U x y
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis T W hW _ _ ?_
  intro a hle
  exact ((moduleSheafHom_app_restrict p hle _).trans
      (congrArg (fun z => (p.val.app (op (W a))).hom z)
        (toTensorSheafSection_restrict X F G hle x y))).trans
    ((h a _ _).trans
      ((moduleSheafHom_app_restrict q hle _).trans
        (congrArg (fun z => (q.val.app (op (W a))).hom z)
          (toTensorSheafSection_restrict X F G hle x y))).symm)

/-- An isomorphism of sheaves of modules is inverted section by section. -/
public theorem moduleSheafIso_hom_app_inv_app {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}
    {A B : SheafOfModules.{u} 𝒪} (E : A ≅ B) {U : Opens X} (w : B.val.obj (op U)) :
    (E.hom.val.app (op U)).hom ((E.inv.val.app (op U)).hom w) = w :=
  congrArg (fun φ => ModuleCat.Hom.hom (SheafOfModules.Hom.val φ |>.app (op U)) w) E.inv_hom_id

/-- **Assertion (1) of Tag 0B5J read forwards on a chart.** The library fixes the isomorphism
`M̃ ≅ i^*(M'~)` by describing its *inverse* on the standard opens
(`associatedModuleSheafVeroneseIso_standardOpen`); the square needs the isomorphism itself. Since
`veroneseModuleAwayEquiv` is bijective, every section of `M̃` over `D₊(f)` is the one named there,
so inverting that description is the whole content. -/
public theorem associatedModuleSheafVeroneseIso_hom_standardOpen
    (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ z : GradedModuleDegreeZeroLocalization
      (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) (veronesePower 𝒮 d f hf),
    let i := veroneseProjIso 𝒮 d hd
    let vf := veronesePower 𝒮 d f hf
    let U := Proj.basicOpen (veroneseGrading 𝒮 d) vf
    let V := Proj.basicOpen 𝒮 f
    let h : i.hom ⁻¹ᵁ U = V := veroneseProjIso_basicOpen 𝒮 d hd f he hf
    let N := ProjectiveSpectrum.Proj.associatedModuleSheaf
      (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)
    let s := (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
      (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)
      (show vf ∈ veroneseGrading 𝒮 d e from by
        change f ^ d ∈ 𝒮 (e * d)
        rw [mul_comm e d]
        simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded d hf) he).symm z
    ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom.val.app (.op V))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
          (veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd z)) =
      h ▸ ((Scheme.Modules.pullbackPushforwardAdjunction i.hom).unit.app N).val.app
        (.op U) s := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  intro z
  exact (congrArg
      (fun t => ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom.val.app
        (.op (Proj.basicOpen 𝒮 f))) t)
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨
          hf he).symm_apply_eq.mpr
        (associatedModuleSheafVeroneseIso_standardOpen 𝒮 𝒨 d hd f he hf z).symm)).trans
    (moduleSheafIso_hom_app_inv_app (associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd) _)

/-! ### The algebraic identity the source's argument reduces to -/

/-- **"Since these maps agree via the identifications `M₍f₎ = M'₍f ᵈ₎`".** This is the algebraic
content of Tag 0B5J's argument for the 01MK compatibility, and it is true: on the chart
`D₊(f ᵈ) ⊆ Proj S⁽ᵈ⁾`, whose preimage under `i` is `D₊(f)`, the multiplication of Tag 01MK sends
`m / (f ᵈ)^j` and `n / (f ᵈ)^k` to a fraction with denominator `(f ᵈ)^(j+k)`, the canonical
comparison `veroneseTensorMap` carries the numerator `m ⊗ n` to the same pure tensor read in
`M ⊗_S N`, and `veroneseModuleAwayEquiv` turns the denominator `(f ᵈ)^(j+k)` into
`f^(d(j+k)) = f^(dj) · f^(dk)` — which is exactly the denominator the multiplication downstairs
produces from `m / f^(dj)` and `n / f^(dk)`.

Note what this does *not* say. It is an identity of fractions, not the equality of graded modules
`M' ⊗_{S'} N' = (M ⊗_S N)'` that the source's proof asserts; that equality is false
(`not_injective_veroneseTensorMap`). What this identity gives is only that both composites
of the square send `m / f^(pd) ⊗ n / f^(qd)` to `c(m ⊗ n) / (f ᵈ)^(p+q)`; it does not make `c`
an isomorphism on localizations. -/
public theorem veroneseLocalizedModuleFun_veroneseTensorMap_mk (d : ℕ) (f : S) {k : ℕ}
    (hf : f ∈ 𝒮 k) (j : ℕ) (m : veroneseSubmodule 𝒮 𝒨 d) (n : veroneseSubmodule 𝒮 𝒩 d) :
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    veroneseLocalizedModuleFun 𝒮 d (tensorGrading (S := S) 𝒨 𝒩) f hf
        (LocalizedModule.mk (veroneseTensorMap 𝒮 𝒨 𝒩 d (m ⊗ₜ[veroneseSubring 𝒮 d] n))
          (⟨veronesePower 𝒮 d f hf ^ j, ⟨j, rfl⟩⟩ :
            Submonoid.powers (veronesePower 𝒮 d f hf))) =
      LocalizedModule.mk ((m : M) ⊗ₜ[S] (n : N))
        (⟨f ^ (d * j), ⟨d * j, rfl⟩⟩ : Submonoid.powers f) := by
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  exact (veroneseLocalizedModuleFun_mk_pow 𝒮 d (tensorGrading (S := S) 𝒨 𝒩) f hf j
      (veroneseTensorMap 𝒮 𝒨 𝒩 d (m ⊗ₜ[veroneseSubring 𝒮 d] n))).trans
    (congrArg (fun t => LocalizedModule.mk t
        (⟨f ^ (d * j), ⟨d * j, rfl⟩⟩ : Submonoid.powers f))
      (veroneseTensorMap_tmul 𝒮 𝒨 𝒩 d m n))

/-- The two denominators the 01MK compatibility produces agree: the multiplication upstairs on
`Proj S⁽ᵈ⁾` accumulates the exponent `d(j + l)`, the one downstairs on `Proj S` accumulates
`d j + d l`. This is the only arithmetic in the square. -/
public theorem mk_pow_mul_add {P : Type u} [AddCommGroup P] [Module S P]
    (f : S) (d j l : ℕ) (t : P) :
    LocalizedModule.mk t (⟨f ^ (d * (j + l)), ⟨d * (j + l), rfl⟩⟩ : Submonoid.powers f) =
      LocalizedModule.mk t
        ((⟨f ^ (d * j), ⟨d * j, rfl⟩⟩ : Submonoid.powers f) * ⟨f ^ (d * l), ⟨d * l, rfl⟩⟩) :=
  congrArg (fun w : Submonoid.powers f => LocalizedModule.mk t w)
    (Subtype.ext ((congrArg (fun z : ℕ => f ^ z) (mul_add d j l)).trans
      (pow_add f (d * j) (d * l))))

/-- **Every element of `M₍f₎` is a single homogeneous fraction `m / f ⁿ`.** The degree-zero
part of the localization is *defined* as the span of such fractions, and
`Stacks.Veronese.mem_gradedModuleDegreeZeroLocalization_iff` says that the span adds nothing:
a sum of homogeneous fractions of degree zero is again one. This is the form
`associatedModuleSheafTensorMap_standardOpen` demands of its input sections, so it is what puts
an arbitrary section over a chart into the shape the 01MK formula is stated at. -/
public theorem exists_degreeZeroFraction {A : Type u} {P : Type u} {ς : Type*} {τ : Type*}
    [CommRing A] [AddCommGroup P] [Module A P]
    [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
    [SetLike τ P] [AddSubgroupClass τ P] (ℒ : ℤ → τ) [Decomposition ℒ]
    [SetLike.GradedSMul 𝒜 ℒ] (f : A) {c : ℕ} (hf : f ∈ 𝒜 c)
    (z : GradedModuleDegreeZeroLocalization 𝒜 ℒ f) :
    ∃ (n : ℕ) (m : P) (hm : m ∈ ℒ (n • (c : ℤ))),
      z = ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf n m hm := by
  obtain ⟨n, m, hm, hz⟩ :=
    (mem_gradedModuleDegreeZeroLocalization_iff 𝒜 ℒ f c hf z.1).mp z.2
  exact ⟨n, m, hm, Subtype.ext hz⟩

/-! ### Tag 01CD on sections, read for the inverse -/

/-- **Tag 01CD on sections, for the inverse of the comparison.** The square's lower-left corner
is reached through `(veronesePullbackTensorIso ...).inv`, whereas Tag 01CD is described on
sections in the forward direction by `schemePullbackTensorIso_hom_modulesPullbackUnit`. This is
that description inverted: the inverse carries the section attached to the pure tensor of two
pulled-back sections to the pullback of the section attached to their pure tensor upstairs.
Stated for an arbitrary morphism of schemes, so that none of the Veronese `letI`s are in scope
while it is elaborated. -/
public theorem schemePullbackTensorIso_inv_toTensorSheafSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : Y.Modules) (U : Y.Opens)
    (x : A.val.obj (op U)) (y : B.val.obj (op U)) :
    Scheme.Modules.Hom.app
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv (g ⁻¹ᵁ U)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
          ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B)
          (op (g ⁻¹ᵁ U))
          (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A U x ⊗ₜ
            Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B U y)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
            ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B))) U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Y.toRingedSpace A B
          (op U) (x ⊗ₜ y)) := by
  rw [← Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit g A B U x y]
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ (g ⁻¹ᵁ U) _)
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).hom_inv_id

/-- **The unit of the module pullback is natural.** Pulling back a section and then applying the
pullback of a morphism is applying the morphism and then pulling back. The square's lower edge is
`(Scheme.Modules.pullback i).map (01MK ≫ veroneseTensorSheafMap)` applied to a pulled-back
section, so this is what moves that edge's work from `Proj S` back to `Proj S⁽ᵈ⁾`, where the
chart formulas live. -/
public theorem modulesPullbackUnit_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Y.Modules} (φ : A ⟶ B) (U : Y.Opens) (s : A.val.obj (op U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map φ) (g ⁻¹ᵁ U)
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A U s) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B U
        (Scheme.Modules.Hom.app φ U s) :=
  (congrArg (fun ψ => Scheme.Modules.Hom.app ψ U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ)).symm

/-- **Transport of a pure tensor across an equality of opens.** The chart description of 0B5J's
assertion (1) lands in `h ▸ (pullback unit)` for `h : i⁻¹ D₊(f ᵈ) = D₊(f)`, while Tag 01CD is
described over `i⁻¹ D₊(f ᵈ)`; moving the pure tensor of two such sections across `h` is this. -/
public theorem toTensorSheafSection_cast (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (_root_.structureSheafRing X))
    {W V : Opens X.carrier} (hWV : W = V)
    (a : F.val.obj (op W)) (b : G.val.obj (op W)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
        ((hWV ▸ a : F.val.obj (op V)) ⊗ₜ[X.presheaf.obj (op V)]
          (hWV ▸ b : G.val.obj (op V))) =
      hWV ▸ Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op W)
        (a ⊗ₜ[X.presheaf.obj (op W)] b) := by
  cases hWV
  rfl

/-- **The lower edge of the square on a chart.** On the standard open of `f ᵈ` in `Proj S⁽ᵈ⁾` the
morphism of associated sheaves induced by `veroneseTensorMap` is the degree-zero part of the
localized comparison, by Tag 01M7's naturality in the graded module. -/
public theorem veroneseTensorSheafMap_standardOpen (d : ℕ) (hd : 0 < d) (f : S) {k : ℕ}
    (he : 0 < k) (hf : f ∈ 𝒮 k) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d k,
    ∀ s : (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (tensorGrading (S := veroneseSubring 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d))).val.obj
          (op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d f hf))),
    ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf he
          ((veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd).val.app _ s) :
        GradedModuleDegreeZeroLocalization (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d)
          (veronesePower 𝒮 d f hf)) :
          LocalizedModule.Away (R := veroneseSubring 𝒮 d) (veronesePower 𝒮 d f hf)
            (veroneseSubmodule 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d)) =
      LocalizedModule.map (Submonoid.powers (veronesePower 𝒮 d f hf))
        (veroneseTensorMap 𝒮 𝒨 𝒩 d)
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (tensorGrading (S := veroneseSubring 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)) hvf he s :
          GradedModuleDegreeZeroLocalization (veroneseGrading 𝒮 d)
            (tensorGrading (S := veroneseSubring 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d))
            (veronesePower 𝒮 d f hf)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  let := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  let := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  let := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  intro hvf s
  exact associatedModuleSheafMap_standardOpen (veroneseGrading 𝒮 d) _ _
    (veroneseTensorMap 𝒮 𝒨 𝒩 d)
    (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d) hvf he s

omit [AddSubgroupClass σ S] [GradedRing 𝒮] [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- The degree an element of `(T⁽ᵈ⁾)ₚ` has in `T`, read for `T` directly: a Veronese-degree-`p`
element of `T⁽ᵈ⁾` sits in `T_{pd·deg f}`, which is Veronese-degree `pd` for the generator `f`
itself. This is the only index arithmetic the Veronese chart comparison needs. -/
public theorem mem_of_mem_veroneseModuleGrading (d p e : ℕ) {x : veroneseSubmodule 𝒮 𝒨 d}
    (hx : x ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ))) :
    (x : M) ∈ 𝒨 ((p * d) • (e : ℤ)) := by
  have h : (p • (e : ℤ)) * d = (p * d) • (e : ℤ) := by
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  exact h ▸ (mem_veroneseModuleGrading 𝒮 𝒨).mp hx

/-- **The Veronese module comparison on a homogeneous fraction.** The identification
`M'₍f ᵈ₎ ≅ M₍f₎` of Tag 0B5J's proof carries the fraction `m / (f ᵈ)^p` to `m / f^(pd)`. Both
sides are written as `degreeZeroFraction`, which is the form the 01MK chart formula is stated
at, so this is the lemma that lets assertion (1)'s chart description and the 01MK chart formula
be applied to the same section. -/
public theorem veroneseModuleAwayEquiv_degreeZeroFraction (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (hf : f ∈ 𝒮 e) (p : ℕ) (mb : veroneseSubmodule 𝒮 𝒨 d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd
        (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d) hvf p mb hmb) =
      ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
        (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  intro hvf
  exact Subtype.ext (veroneseModuleAwayEquiv_mk 𝒮 d 𝒨 f hf hd p mb _ rfl)

/-! ### The two sides of the square, read on an element -/

/-- The left side of the square, applied to a section: multiply by Tag 01MK, then transport by
assertion (1). Pinned once as a named lemma, so that the definitional unfolding of the composite
is paid here rather than rediscovered at every occurrence. -/
public theorem veroneseTensorSquareLeft_app (d : ℕ) (hd : 0 < d)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    ((veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd).val.app U).hom z =
      ((associatedModuleSheafVeroneseIso 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd).hom.val.app U).hom
        (((associatedModuleSheafTensorMap 𝒮 𝒨 𝒩).val.app U).hom z) :=
  rfl

/-- The right side of the square, applied to a section: transport both factors by assertion (1),
cross Tag 01CD, then multiply upstairs and apply the comparison. Pinned once as a named lemma,
for the same reason as `veroneseTensorSquareLeft_app`. -/
public theorem veroneseTensorSquareRight_app (d : ℕ) (hd : 0 < d)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ((veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd).val.app U).hom z =
      (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (associatedModuleSheafTensorMap (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) ≫
              veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd)).val.app U).hom
        (((veronesePullbackTensorIso 𝒮 d hd
              (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d))
              (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒩 d))).inv.val.app U).hom
          (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
              (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
      (X := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨,
        ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩))
      (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d)),
        (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒩 d))))
      ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom,
        (associatedModuleSheafVeroneseIso 𝒮 𝒩 d hd).hom))).val.app U).hom z)) :=
  rfl

/-! ### Assertion (1) on a chart, both sides written as fractions -/

/-- **Assertion (1) of Tag 0B5J on a chart, with both sides written as homogeneous fractions.**
The isomorphism `M̃ ≅ i^*(M'~)` carries the section `m / f^(pd)` of `M̃` over `D₊(f)`, whose
numerator is Veronese-homogeneous of degree `p`, to the pullback of the section `m / (f ᵈ)^p` of
`M'~` over `D₊(f ᵈ)`.

This is `associatedModuleSheafVeroneseIso_hom_standardOpen` with its input rewritten through
`veroneseModuleAwayEquiv_degreeZeroFraction`, so that the section it is stated at is in the form
Tag 01MK's chart formula consumes. -/
public theorem associatedModuleSheafVeroneseIso_hom_degreeZeroFraction (d : ℕ) (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p : ℕ) (mb : veroneseSubmodule 𝒮 𝒨 d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom.val.app (op (Proj.basicOpen 𝒮 f)))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
            (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) hvf p mb hmb)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  intro hvf
  refine Eq.trans (congrArg (fun t => ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom.val.app
        (op (Proj.basicOpen 𝒮 f)))
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm t))
    (veroneseModuleAwayEquiv_degreeZeroFraction 𝒮 𝒨 d hd f hf p mb hmb hvf).symm) ?_
  exact associatedModuleSheafVeroneseIso_hom_standardOpen 𝒮 𝒨 d hd f he hf _

/-- `degreeZeroFraction` is determined by its exponent and its numerator: the degree hypothesis
is a proposition and so contributes nothing to the value. -/
public theorem degreeZeroFraction_congr {A : Type u} {P : Type u} {ς : Type*} {τ : Type*}
    [CommRing A] [AddCommGroup P] [Module A P]
    [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
    [SetLike τ P] [AddSubgroupClass τ P] (ℒ : ℤ → τ) [Decomposition ℒ]
    [SetLike.GradedSMul 𝒜 ℒ] {f : A} {c : ℕ} (hf : f ∈ 𝒜 c) {n n' : ℕ} {m m' : P}
    (hn : n = n') (hm : m = m')
    (h1 : m ∈ ℒ (n • (c : ℤ))) (h2 : m' ∈ ℒ (n' • (c : ℤ))) :
    ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf n m h1 =
      ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf n' m' h2 := by
  subst hn
  subst hm
  rfl

/-- **The left side of the square on a chart.** On `D₊(f)`, applied to the pure tensor of the
fractions `m / f^(pd)` and `n / f^(qd)` whose numerators are Veronese-homogeneous of degrees `p`
and `q`, the composite "multiply by Tag 01MK, then transport by assertion (1)" is the pullback of
the section `c(m ⊗ n) / (f ᵈ)^(p+q)` of `((M ⊗_S N)⁽ᵈ⁾)~` over `D₊(f ᵈ) ⊆ Proj S⁽ᵈ⁾`.

The two steps are Tag 01MK's chart formula, which adds the exponents to `pd + qd`, and the
chartwise description of assertion (1), which reads `pd + qd = (p+q)d` as the Veronese
identification `M₍f₎ = M'₍f ᵈ₎` does. The numerator moves across by
`veroneseTensorMap_tmul`: the canonical comparison `c` carries `m ⊗ n` computed in `M⁽ᵈ⁾ ⊗ N⁽ᵈ⁾`
to the same pure tensor read in `M ⊗_S N`. -/
public theorem veroneseTensorSquareLeft_standardOpen (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 𝒩 d) (hnb : nb ∈ veroneseModuleGrading 𝒮 𝒩 d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)
          (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒩 hf (q * d) (nb : N)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒩 d q e hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf (p + q)
              (veroneseTensorMap 𝒮 𝒨 𝒩 d (mb ⊗ₜ[veroneseSubring 𝒮 d] nb))
              (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d ((p + q) • (e : ℤ))
                (mb ⊗ₜ[veroneseSubring 𝒮 d] nb)
                (Stacks.GradedModule.tmul_mem_tensorGrading
                  (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
                  (add_nsmul (e : ℤ) p q).symm hmb hnb)))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  let := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  let := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  let := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  intro hvf
  refine (veroneseTensorSquareLeft_app 𝒮 𝒨 𝒩 d hd _ _).trans ?_
  refine Eq.trans (congrArg (fun t => ((associatedModuleSheafVeroneseIso 𝒮
        (tensorGrading (S := S) 𝒨 𝒩) d hd).hom.val.app (op (Proj.basicOpen 𝒮 f))).hom t)
      (associatedModuleSheafTensorMap_standardOpen 𝒮 𝒨 𝒩 hf he (p * d) (q * d)
        (mb : M) (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)
        (nb : N) (mem_of_mem_veroneseModuleGrading 𝒮 𝒩 d q e hnb))) ?_
  refine Eq.trans (congrArg (fun t => ((associatedModuleSheafVeroneseIso 𝒮
        (tensorGrading (S := S) 𝒨 𝒩) d hd).hom.val.app (op (Proj.basicOpen 𝒮 f))).hom
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
          (tensorGrading (S := S) 𝒨 𝒩) hf he).symm t))
      (degreeZeroFraction_congr 𝒮 (tensorGrading (S := S) 𝒨 𝒩) hf (add_mul p q d).symm
        (veroneseTensorMap_tmul 𝒮 𝒨 𝒩 d mb nb).symm
        (Stacks.GradedModule.tmul_mem_tensorGrading 𝒨 𝒩
          (add_nsmul (e : ℤ) (p * d) (q * d)).symm
          (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)
          (mem_of_mem_veroneseModuleGrading 𝒮 𝒩 d q e hnb))
        (mem_of_mem_veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d (p + q) e
          (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d ((p + q) • (e : ℤ))
            (mb ⊗ₜ[veroneseSubring 𝒮 d] nb)
            (Stacks.GradedModule.tmul_mem_tensorGrading
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
              (add_nsmul (e : ℤ) p q).symm hmb hnb))))) ?_
  exact associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮
    (tensorGrading (S := S) 𝒨 𝒩) d hd f he hf (p + q)
    (veroneseTensorMap 𝒮 𝒨 𝒩 d (mb ⊗ₜ[veroneseSubring 𝒮 d] nb))
    (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d ((p + q) • (e : ℤ))
      (mb ⊗ₜ[veroneseSubring 𝒮 d] nb)
      (Stacks.GradedModule.tmul_mem_tensorGrading
        (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
        (add_nsmul (e : ℤ) p q).symm hmb hnb)) hvf

/-! ### The lower-left path of the square, with no Veronese data in it -/

/-- **The square's lower-left path, for an arbitrary morphism of schemes.** Starting from the
canonical section attached to the pure tensor of two *pulled-back* sections over `g⁻¹U`,
transported across an equality `g⁻¹U = V` of opens: crossing Tag 01CD backwards and then applying
the pullback of any morphism `φ` out of the tensor product is the same as doing `φ` upstairs on
the pure tensor and pulling the result back.

This is the whole lower-left path of the 01MK square — the two casts, Tag 01CD on sections and
the naturality of the pullback unit — in one step, and deliberately stated for an arbitrary
`g : X ⟶ Y`: the square's own objects carry `letI`-bound grading instances, so none of this may
be elaborated with the Veronese data in scope. -/
public theorem pullbackMap_schemePullbackTensorIso_inv_cast {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B C : Y.Modules)
    (φ : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B)) :
      Y.Modules) ⟶ C)
    (U : Y.Opens) {V : X.Opens} (h : g ⁻¹ᵁ U = V)
    (x : A.val.obj (op U)) (y : B.val.obj (op U)) :
    (((Scheme.Modules.pullback g).map φ).val.app (op V))
        (((Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv.val.app (op V))
          (h ▸ Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            X.toRingedSpace ((Scheme.Modules.pullback g).obj A)
            ((Scheme.Modules.pullback g).obj B) (op (g ⁻¹ᵁ U))
            (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A U x ⊗ₜ
              Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B U y))) =
      h ▸ Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g C U
        (Scheme.Modules.Hom.app φ U
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            Y.toRingedSpace A B (op U) (x ⊗ₜ y))) := by
  refine Eq.trans (congrArg (fun w => (((Scheme.Modules.pullback g).map φ).val.app (op V)) w)
    (moduleSheafHom_app_cast
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv h _)) ?_
  refine Eq.trans (congrArg (fun w => (((Scheme.Modules.pullback g).map φ).val.app (op V))
      (h ▸ w)) (schemePullbackTensorIso_inv_toTensorSheafSection g A B U x y)) ?_
  refine Eq.trans (moduleSheafHom_app_cast ((Scheme.Modules.pullback g).map φ) h _) ?_
  exact congrArg (fun w => h ▸ w) (modulesPullbackUnit_naturality g φ U _)

/-- **The square's left edge, for arbitrary morphisms of sheaves of modules.** If `φ` and `ψ`
carry two sections over `V` to transports across `h : W = V` of two sections over `W`, then
`φ ⊗ ψ` carries the canonical section attached to their pure tensor to the transport of the one
attached to the pure tensor over `W`.

Stated with no Veronese data: with the square's objects in scope the same argument run by `rw`
exhausts the heartbeat allowance of a single declaration. The Veronese instance is this lemma
applied to the two halves of `associatedModuleSheafVeroneseIso_hom_degreeZeroFraction`. -/
public theorem tensorSheafMap_app_toTensorSheafSection_cast
    (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    (F G F' G' : SheafOfModules.{u} (_root_.structureSheafRing X))
    (φ : F ⟶ F') (ψ : G ⟶ G') {W V : Opens X.carrier} (h : W = V)
    (x : F.val.obj (op V)) (y : G.val.obj (op V))
    (a : F'.val.obj (op W)) (b : G'.val.obj (op W))
    (hx : (φ.val.app (op V)).hom x = h ▸ a) (hy : (ψ.val.app (op V)).hom y = h ▸ b) :
    ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((φ, ψ) : (_, _) ⟶ (_, _)))).val.app (op V)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
          (x ⊗ₜ[X.presheaf.obj (op V)] y)) =
      h ▸ Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F' G' (op W)
        (a ⊗ₜ[X.presheaf.obj (op W)] b) := by
  cases h
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      X F G F' G' φ ψ _ x y).trans
    (congrArg₂ (fun u v => Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
      X F' G' _ (u ⊗ₜ v)) hx hy)

/-- A composite of morphisms of sheaves of modules is applied to a section one factor at a
time. -/
public theorem moduleSheafHom_comp_app {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}
    {A B C : SheafOfModules.{u} 𝒪} (φ : A ⟶ B) (ψ : B ⟶ C) {U : Opens X}
    (s : A.val.obj (op U)) :
    ((φ ≫ ψ).val.app (op U)).hom s = (ψ.val.app (op U)).hom ((φ.val.app (op U)).hom s) :=
  rfl

/-! ### The square's lower edge on a chart -/

/-- **The square's lower edge on a chart, on a homogeneous fraction.** The morphism of associated
sheaves induced by the canonical comparison `c : M⁽ᵈ⁾ ⊗ N⁽ᵈ⁾ ⟶ (M ⊗_S N)⁽ᵈ⁾` sends the section
`w / (f ᵈ)^k` to `c(w) / (f ᵈ)^k`: it acts on the numerator and leaves the denominator alone.
This is `veroneseTensorSheafMap_standardOpen` — the degree-zero part of the localized comparison
— read on a single fraction via `LocalizedModule.map_mk`. -/
public theorem veroneseTensorSheafMap_degreeZeroFraction (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e) (k : ℕ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ∀ w : veroneseSubmodule 𝒮 𝒨 d ⊗[veroneseSubring 𝒮 d] veroneseSubmodule 𝒮 𝒩 d,
    ∀ hw : w ∈ tensorGrading (S := veroneseSubring 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) (k • (e : ℤ)),
    ((veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd).val.app
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))).hom
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
            (tensorGrading (S := veroneseSubring 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)) hvf he).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
            (tensorGrading (S := veroneseSubring 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)) hvf k w hw)) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf he).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf k
          (veroneseTensorMap 𝒮 𝒨 𝒩 d w)
          (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d (k • (e : ℤ)) w hw)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  let := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  let := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  let := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  intro hvf w hw
  refine (LinearEquiv.eq_symm_apply _).mpr (Subtype.ext ?_)
  refine (veroneseTensorSheafMap_standardOpen 𝒮 𝒨 𝒩 d hd f he hf hvf _).trans ?_
  rw [LinearEquiv.apply_symm_apply]
  exact LocalizedModule.map_mk _ _ _ _

/-- **The square's upper and lower edges composed, upstairs on a chart.** On `D₊(f ᵈ)` in
`Proj S⁽ᵈ⁾`, multiplying `m / (f ᵈ)^p` by `n / (f ᵈ)^q` with Tag 01MK and then applying the
comparison `c` gives `c(m ⊗ n) / (f ᵈ)^(p+q)`. This is the value the left side of the square
reaches by `veroneseTensorSquareLeft_standardOpen`, read upstairs. -/
public theorem veroneseTensorUpstairs_standardOpen (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 𝒩 d) (hnb : nb ∈ veroneseModuleGrading 𝒮 𝒩 d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((associatedModuleSheafTensorMap (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) ≫
            veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd).val.app
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj (veroneseGrading 𝒮 d)).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d))
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒩 d))
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d) hvf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d) hvf p mb hmb) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒩 d) hvf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒩 d) hvf q nb hnb))) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf he).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf (p + q)
          (veroneseTensorMap 𝒮 𝒨 𝒩 d (mb ⊗ₜ[veroneseSubring 𝒮 d] nb))
          (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d ((p + q) • (e : ℤ))
            (mb ⊗ₜ[veroneseSubring 𝒮 d] nb)
            (Stacks.GradedModule.tmul_mem_tensorGrading
              (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
              (add_nsmul (e : ℤ) p q).symm hmb hnb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  let := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  let := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  let := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  intro hvf
  refine (moduleSheafHom_comp_app _ _ _).trans ?_
  refine Eq.trans (congrArg (fun t => ((veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd).val.app
        (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))).hom t)
      (associatedModuleSheafTensorMap_standardOpen (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) hvf he p q
        mb hmb nb hnb)) ?_
  exact veroneseTensorSheafMap_degreeZeroFraction 𝒮 𝒨 𝒩 d hd f he hf (p + q) hvf
    (mb ⊗ₜ[veroneseSubring 𝒮 d] nb) _

/-- **The right side of the square on a chart.** On `D₊(f)`, applied to the pure tensor of
`m / f^(pd)` and `n / f^(qd)`, the composite "transport both factors by assertion (1), cross Tag
01CD, multiply upstairs, apply the comparison" is the pullback of the section
`c(m ⊗ n) / (f ᵈ)^(p+q)` over `D₊(f ᵈ)`.

`Stacks.Tag01VSPullbackTensor.modulesPullbackUnit` is by definition the component of the
pullback-pushforward unit, so this is the same value that
`veroneseTensorSquareLeft_standardOpen` computes for the left side — which is the commutativity
of the square on that chart. -/
public theorem veroneseTensorSquareRight_standardOpen (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 𝒩 d) (hnb : nb ∈ veroneseModuleGrading 𝒮 𝒩 d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    letI := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
    letI := tensorGrading_decomposition (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    letI := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)
          (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒩 hf (q * d) (nb : N)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒩 d q e hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d) hvf (p + q)
              (veroneseTensorMap 𝒮 𝒨 𝒩 d (mb ⊗ₜ[veroneseSubring 𝒮 d] nb))
              (veroneseTensorMap_mem_veroneseModuleGrading 𝒮 𝒨 𝒩 d ((p + q) • (e : ℤ))
                (mb ⊗ₜ[veroneseSubring 𝒮 d] nb)
                (Stacks.GradedModule.tmul_mem_tensorGrading
                  (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
                  (add_nsmul (e : ℤ) p q).symm hmb hnb)))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  let := veroneseModuleGradingDecomposition 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  let := tensorGrading_decomposition (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  let := tensorGrading_gradedSMul (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d)
  intro hvf
  refine (veroneseTensorSquareRight_app 𝒮 𝒨 𝒩 d hd _ _).trans ?_
  refine Eq.trans (congrArg (fun w =>
      (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (associatedModuleSheafTensorMap (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) ≫
              veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd)).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (((veronesePullbackTensorIso 𝒮 d hd
                (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                  (veroneseModuleGrading 𝒮 𝒨 d))
                (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                  (veroneseModuleGrading 𝒮 𝒩 d))).inv.val.app
            (op (Proj.basicOpen 𝒮 f))).hom w))
    (tensorSheafMap_app_toTensorSheafSection_cast
      (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace _ _ _ _
      (associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom
      (associatedModuleSheafVeroneseIso 𝒮 𝒩 d hd).hom
      (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _ _ _
      (associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮 𝒨 d hd f he hf p mb hmb hvf)
      (associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮 𝒩 d hd f he hf q nb hnb
        hvf))) ?_
  refine (pullbackMap_schemePullbackTensorIso_inv_cast (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d))
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒩 d))
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d))
    (associatedModuleSheafTensorMap (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d) (veroneseModuleGrading 𝒮 𝒩 d) ≫
      veroneseTensorSheafMap 𝒮 𝒨 𝒩 d hd)
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _).trans ?_
  exact congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 (tensorGrading (S := S) 𝒨 𝒩) d))
        (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)) t)
    (veroneseTensorUpstairs_standardOpen 𝒮 𝒨 𝒩 d hd f he hf p q mb hmb nb hnb hvf)

/-! ### The square commutes -/

/-- Every section of `M̃` over `D₊(f)` is the one attached to a homogeneous fraction `m / f^(pd)`
whose numerator `m` lies in `M⁽ᵈ⁾` with Veronese-degree `p`. -/
private theorem exists_eq_symm_degreeZeroFraction (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e)
    (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (Proj.basicOpen 𝒮 f))) :
    ∃ (p : ℕ) (mb : veroneseSubmodule 𝒮 𝒨 d)
      (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ))),
      x = (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
          (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  obtain ⟨p, mb, hmb, hz⟩ := exists_degreeZeroFraction (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veronesePower 𝒮 d f hf) hvf
    ((veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd).symm
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he x))
  refine ⟨p, mb, hmb, ?_⟩
  exact ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
        𝒮 𝒨 hf he).symm_apply_apply x).symm.trans
      (congrArg (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
        ((((veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd).apply_symm_apply _).symm.trans
            (congrArg (veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd) hz)).trans
          (veroneseModuleAwayEquiv_degreeZeroFraction 𝒮 𝒨 d hd f hf p mb hmb hvf)))

/-- **The 01MK square commutes on every chart, on every pure tensor of sections.** An arbitrary
section of `M̃` over `D₊(f)` is a single homogeneous fraction `m / f ⁿ`
(`exists_degreeZeroFraction`), and the Veronese identification `M₍f₎ = M'₍f ᵈ₎` puts its
numerator in `M⁽ᵈ⁾` and its exponent in `dℕ`; so the two chart computations
`veroneseTensorSquareLeft_standardOpen` and `veroneseTensorSquareRight_standardOpen` apply, and
they return the same value. -/
public theorem veroneseTensorCompatibility_chart (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ}
    (he : 0 < e) (hf : f ∈ 𝒮 e)
    (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (Proj.basicOpen 𝒮 f)))
    (y : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩).val.obj
      (op (Proj.basicOpen 𝒮 f))) :
    ((veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)
          (op (Proj.basicOpen 𝒮 f)) (x ⊗ₜ y)) =
      ((veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩)
          (op (Proj.basicOpen 𝒮 f)) (x ⊗ₜ y)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒩 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  obtain ⟨p, mb, hmb, rfl⟩ := exists_eq_symm_degreeZeroFraction 𝒮 𝒨 d hd f he hf x
  obtain ⟨q, nb, hnb, rfl⟩ := exists_eq_symm_degreeZeroFraction 𝒮 𝒩 d hd f he hf y
  exact (veroneseTensorSquareLeft_standardOpen 𝒮 𝒨 𝒩 d hd f he hf p q mb hmb nb hnb hvf).trans
    (veroneseTensorSquareRight_standardOpen 𝒮 𝒨 𝒩 d hd f he hf p q mb hmb nb hnb hvf).symm

/-- **The compatibility of Tag 0B5J's assertion (1) with the multiplication maps of Tag 01MK.**
The square of this file commutes: for graded `S`-modules `M` and `N`, the canonical isomorphisms
`M̃ ≅ i^*(M'~)`, `Ñ ≅ i^*(N'~)` and `(M ⊗_S N)~ ≅ i^*(((M ⊗_S N)')~)` of assertion (1) carry the
multiplication map of Tag 01MK on `Proj S` to the one on `Proj S⁽ᵈ⁾` followed by the associated
sheaf map of the canonical comparison `c : M' ⊗_{S'} N' ⟶ (M ⊗_S N)'`.

The proof is the source's own: both sides are morphisms of sheaves of modules out of a
sheafified tensor product, so they agree as soon as they agree on pure tensors of sections over
the standard opens of positive-degree homogeneous elements
(`tensorSheaf_hom_ext_onBasis_tmul`), and over `D₊(f) = i⁻¹D₊(f ᵈ)` both send `m / f^(pd)` and
`n / f^(qd)` to `c(m ⊗ n) / (f ᵈ)^(p+q)` — "these maps agree via the identifications
`M₍f₎ = M'₍f ᵈ₎`".

The comparison `c` on the lower edge is not an identification: the equality
`M' ⊗_{S'} N' = (M ⊗_S N)'` that the source asserts at this point is false, refuted by
`Stacks.Veronese.not_injective_veroneseTensorMap`, which shows that `c` itself is not injective
at `S = k[x, y]`, `d = 2`, `M = N = S(1)`. The square commutes with `c` inserted:
over every standard open both composites send `m / f^(pd) ⊗ n / f^(qd)` to
`c(m ⊗ n) / (f ᵈ)^(p+q)`, the identity of fractions recorded by
`veroneseLocalizedModuleFun_veroneseTensorMap_mk`. -/
public theorem veroneseTensorCompatibility (d : ℕ) (hd : 0 < d) :
    VeroneseTensorCompatibility 𝒮 𝒨 𝒩 d hd :=
  tensorSheaf_hom_ext_onBasis_tmul (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
    _ _ _ _ _ _ (isBasis_range_basicOpen_of_pos 𝒮)
    (fun a x y => veroneseTensorCompatibility_chart 𝒮 𝒨 𝒩 d hd a.1.1 a.2.1 a.2.2 x y)

end Stacks.Veronese

end
