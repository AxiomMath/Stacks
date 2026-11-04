module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionsChartPullback

/-!
# The ring of regular functions over a chart, at the spelling the tensor products use

The ring `𝒪_F(V)` of regular functions over an étale scheme chart appears in this development
under **four** names, all definitionally the same ring and none of which instance search
bridges to another:

* `AlgebraicGeometry.Space.chartRing B S hS F hF V`, from the small étale ringed site;
  `AlgebraicGeometry.Space.chartMeromorphicAlgebra` is stated over it.
* `(Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj (op V)`,
  from the `PresheafOfModules` structure of an `𝒪_F`-module, which is where the module structure
  on `M(V)` is stored.
* `(ringPresheaf (structureSheaf B S hS F hF).obj).obj (op V)`, with `ringPresheaf` from
  `Stacks.PresheafOfModules.ChangeOfRings`: from
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsObj` of Stacks 03CU, hence the sections of
  `AlgebraicGeometry.Space.meromorphicSectionModule`, and
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorAppIso`.
* `(structureRingPresheaf (structureSheaf B S hS F hF).obj).obj (op V)`, with
  `structureRingPresheaf` from `Stacks.SheafOfModules.TensorSheafification`: from the tensor
  product presheaf and the sheafification unit of Stacks 05NA, hence
  `AlgebraicGeometry.Space.picardTensorModule`.

The first two are what the library's API is stated over; the last two are what any construction
combining meromorphic sections with the tensor product of `𝒪_F`-modules is forced into. The
mismatch is invisible inside a definition whose result type is ascribed — elaboration
propagates the expected type and the instances come with it — and appears only in the
*statement* of a lemma, where there is no expected type to propagate from and every tensor
`a ⊗ₜ[R] m` written by hand needs its `Module R` instance at the spelling written.

This file supplies three bridges, with the library's instances as their witnesses. None of them is
new mathematics: two are the same module and the same algebra at the third spelling of
`𝒪_F(V)` above, and the third is the module structure on the meromorphic sections of an
`𝒪_F`-module read over the `CommRingCat` spelling of `𝒦_F(V)` — exactly as
`AlgebraicGeometry.Space.chartMeromorphicAlgebra` is
`AlgebraicGeometry.Space.chartLocalizationAlgebra`'s notion at a second spelling of the ring of
meromorphic functions.

## Main definitions

* `AlgebraicGeometry.Space.tensorChartRing` is `𝒪_F(V)` at the change-of-rings spelling.
* `AlgebraicGeometry.Space.tensorChartModule` is the `𝒪_F(V)`-module structure on `M(V)` there.
* `AlgebraicGeometry.Space.tensorChartMeromorphicAlgebra` is the `𝒪_F(V)`-algebra structure on
  `𝒦_F(V)` there.
* `AlgebraicGeometry.Space.tensorChartMeromorphicSectionModule` is the `𝒦_F(V)`-module
  structure on the meromorphic sections of `M` over `V`, at the `CommRingCat` spelling of
  `𝒦_F(V)`.

## Implementation notes

None of the bridges is a global instance, and none should be restated in a consumer: all three
are declared once, here, and a consumer pins them with
`attribute [local instance] AlgebraicGeometry.Space.tensorChartModule`,
`attribute [local instance] AlgebraicGeometry.Space.tensorChartMeromorphicAlgebra` and
`attribute [local instance] AlgebraicGeometry.Space.tensorChartMeromorphicSectionModule`, as the
consumers of `AlgebraicGeometry.Space.chartMeromorphicAlgebra` do for it. Making them global
would put two syntactically different `Module 𝒪_F(V) M(V)` instances in scope at once, which is
what the `@[instance_reducible]` attribute on those algebras exists to avoid.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The ring `𝒪_F(V)` of regular functions over an étale chart, at the spelling the
change-of-rings functor of Stacks 03CU and the tensor product presheaf are stated over. This is
`AlgebraicGeometry.Space.chartRing` again; only the spelling of the type differs. -/
abbrev tensorChartRing (V : SmallEtale B S hS F) : Type u :=
  (ringPresheaf (structureSheaf B S hS F hF).obj).obj (op V)

/-- **The module structure on the sections of an `𝒪_F`-module over a chart, at the
change-of-rings spelling of `𝒪_F(V)`.** The module structure is the one the
`PresheafOfModules` structure of `M` carries; this is it, read over
`AlgebraicGeometry.Space.tensorChartRing`.

Not an instance: it is the same module structure as the one instance search already finds at
the ringed-site spelling of `𝒪_F(V)`, and having both in scope globally would leave two
syntactically different instances to choose between. Pin it with
`attribute [local instance]`. -/
@[instance_reducible]
def tensorChartModule (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    Module (tensorChartRing B S hS F hF V) ↥(M.val.obj (op V)) :=
  inferInstanceAs (Module (chartRing B S hS F hF V) ↥(M.val.obj (op V)))

/-- **The `𝒪_F(V)`-algebra structure on the meromorphic functions over a chart, at the
change-of-rings spelling of `𝒪_F(V)`.** This is
`AlgebraicGeometry.Space.chartMeromorphicAlgebra` at that spelling.

Not an instance, for the reason recorded on
`AlgebraicGeometry.Space.chartMeromorphicAlgebra` and on
`AlgebraicGeometry.Space.tensorChartModule`. -/
@[instance_reducible]
def tensorChartMeromorphicAlgebra (V : SmallEtale B S hS F) :
    Algebra (tensorChartRing B S hS F hF V)
      ↥((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) :=
  chartMeromorphicAlgebra B S hS F hF V

/-- **The `𝒦_F(V)`-module structure on the meromorphic sections of an `𝒪_F`-module over a
chart, at the `CommRingCat` spelling of `𝒦_F(V)`.** The sections of
`AlgebraicGeometry.Space.meromorphicSectionModule` over `V` are a module over the ring of
meromorphic functions there; the structure is the one the change-of-rings presheaf of Stacks
03CU carries, and this is it read over the spelling of `𝒦_F(V)` in which
`AlgebraicGeometry.Space.meromorphicChartSheaf` states it, rather than over the underlying
presheaf of rings.

The same remark applies as to `AlgebraicGeometry.Space.tensorChartModule`: the two spellings of
`𝒦_F(V)` are definitionally the same ring and instance search does not bridge them, so this is
needed in the statement of any lemma that writes a tensor of meromorphic sections over
`𝒦_F(V)` by hand. Not an instance; pin it with `attribute [local instance]`. -/
@[instance_reducible]
def tensorChartMeromorphicSectionModule (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) :
    Module ↥((meromorphicChartSheaf B S hS F hF).obj.obj (op V))
      ↥((meromorphicSectionModule B S hS F hF M).obj (op V)) :=
  inferInstanceAs (Module ↥((ringPresheaf (meromorphicChartSheaf B S hS F hF).obj).obj (op V))
    ↥((meromorphicSectionModule B S hS F hF M).obj (op V)))

end AlgebraicGeometry.Space

end
