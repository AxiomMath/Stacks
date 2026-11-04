module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroupAdditivity
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor

/-!
# Objects of a dimension layer, and the support of a tensor product

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project. An
object of `Stacks.Chow.CoherentModulesDimLE C f b` is a module together with two proofs: that it
is coherent, in the spelling the closure theory of coherent modules uses, and that the
delta-dimension of its support is at most `b`. `Stacks.Chow.layerMk` assembles one from a module
carrying the `AlgebraicGeometry.SheafOfModules.IsCoherent` instance that the schemes material
uses, which is the shape every construction in chapter 42 produces.

Tensoring does not enlarge the support, so a bound on the delta-dimension of the support of `ℱ`
is a bound for `ℱ ⊗ ℒ` as well, for an arbitrary `ℒ`. Together with coherence of `ℱ ⊗ ℒ` for
invertible `ℒ` this puts the tensor product in the same layer as `ℱ`.

## Main definitions

* `Stacks.Chow.layerMk` — an object of a dimension layer from a coherent module and a bound.

## Main results

* `Stacks.Chow.supp_tensorModules_subset` — the support of a tensor product is contained in the
  support of the first factor.
* `Stacks.Chow.schemeDeltaDimension_reducedSupport_tensorModules_le` — a delta-dimension bound on
  the support of `ℱ` is one on the support of `ℱ ⊗ ℒ`.
* `Stacks.Chow.isCoherent_tensorModules_of_isInvertible` — `ℱ ⊗ ℒ` is coherent for invertible
  `ℒ`, at the `AlgebraicGeometry.tensorModules` spelling.
* `Stacks.Chow.layerMkTensor` — the tensor product of a layer object with an invertible module,
  as an object of the same layer.

## Implementation notes

The three spellings of the tensor product of two modules on a scheme that chapter 42 and its
neighbours use — `AlgebraicGeometry.tensorModules`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` at the underlying ringed space, and
`Stacks.SheafOfModules.Invertible.tensorProduct` at the structure sheaf and its sheaf condition —
are the same term, so no conversion is performed below; the statements are given at
`AlgebraicGeometry.tensorModules` and apply verbatim to the others.

The two coherence predicates for a sheaf of modules are also the same two fields, and
`AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent` copies between them; since
both are propositions, the proof `Stacks.Chow.layerMk` carries is irrelevant and the support bound
it is handed is accepted unchanged.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-! ### Building an object of a layer -/

/-- An object of the dimension layer `Coh_{≤b}(𝒪_X)` from a coherent `𝒪_X`-module and a bound on
the delta-dimension of its support. -/
def layerMk (b : ℤ) (M : X.Modules) [hM : M.IsCoherent]
    (hdim : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (b : EInt)) :
    CoherentModulesDimLE C f b :=
  ⟨⟨M, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hM⟩, hdim⟩

/-- The underlying module of `layerMk C f b M hdim` is `M`. -/
@[simp]
theorem layerMk_obj_obj (b : ℤ) (M : X.Modules) [M.IsCoherent]
    (hdim : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (b : EInt)) :
    (layerMk C f b M hdim).obj.obj = M :=
  rfl

/-! ### The support of a tensor product -/

/-- **The support of a tensor product is contained in the support of the first factor.** -/
theorem supp_tensorModules_subset (M L : X.Modules) :
    SheafOfModules.supp (tensorModules M L) ⊆ SheafOfModules.supp M := by
  intro y hy
  by_contra h
  exact notMem_supp_tensorSheaf_of_notMem_supp M L h hy

/-- **Tensoring does not raise the delta-dimension of the support.** A bound for `ℱ` is a bound
for `ℱ ⊗ ℒ`, for an arbitrary `ℒ`. -/
theorem schemeDeltaDimension_reducedSupport_tensorModules_le (M L : X.Modules) [M.IsCoherent]
    [(tensorModules M L).IsCoherent] {b : ℤ}
    (hM : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (b : EInt)) :
    schemeDeltaDimension C ((reducedSupport (tensorModules M L)).subschemeι ≫ f) ≤ (b : EInt) :=
  schemeDeltaDimension_reducedSupport_le C f _ fun _ hx =>
    relativeDimension_le_of_mem_supp C f M hM (supp_tensorModules_subset M L hx)

/-- The tensor product of a coherent module with an invertible module is coherent, at the
`AlgebraicGeometry.tensorModules` spelling. -/
theorem isCoherent_tensorModules_of_isInvertible (M L : X.Modules) [M.IsCoherent]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    (tensorModules M L).IsCoherent :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X M L

/-- **The tensor product of a layer object with an invertible module, in the same layer.** -/
def layerMkTensor (b : ℤ) (M : X.Modules) [M.IsCoherent] (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hdim : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (b : EInt)) :
    CoherentModulesDimLE C f b :=
  haveI := isCoherent_tensorModules_of_isInvertible M L hL
  layerMk C f b (tensorModules M L)
    (schemeDeltaDimension_reducedSupport_tensorModules_le C f M L hdim)

/-- The underlying module of `layerMkTensor C f b M L hL hdim` is `tensorModules M L`. -/
@[simp]
theorem layerMkTensor_obj_obj (b : ℤ) (M : X.Modules) [M.IsCoherent] (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hdim : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (b : EInt)) :
    (layerMkTensor C f b M L hL hdim).obj.obj = tensorModules M L :=
  rfl

end Stacks.Chow

end
