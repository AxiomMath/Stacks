module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Boundedness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietorisTriangle
public import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded Mayer--Vietoris triangle as a Mayer--Vietoris apex

For opens `U`, `V` of a scheme `X` and an object `K` of the unbounded derived category `D(𝒪_X)`
there is a distinguished triangle

`Rj_{U ∪ V,*}(K|_{U ∪ V}) ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶`,

and when `U` and `V` cover `X` its first term is `K` itself. This is [Stacks, Tag 08BV]. This file
reads the triangle, constructed in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnboundedMayerVietorisTriangle.lean`, in
the vocabulary `Stacks.Duality.Coherator.IsMayerVietorisApex` of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/Boundedness.lean`, which is the shape the
amplitude estimates of the coherator consume.

## Main results

* `Stacks.Duality.Coherator.isMayerVietorisApex_restrictPushforward_sup` — **[Stacks, Tag 08BV]**
  with apex `Rj_{U ∪ V,*}(K|_{U ∪ V})`, for arbitrary opens `U`, `V`.
* `Stacks.Duality.Coherator.isMayerVietorisApex_self` — **[Stacks, Tag 08BV]** with apex `K`, for
  a cover `U ∪ V = X`.

## Implementation notes

`Stacks.Duality.Coherator.IsMayerVietorisApex` asks only for the existence of the three maps of
the triangle, which is all the amplitude estimates use, and it is stated with the terms
`Stacks.Duality.Coherator.restrictPushforward W K`; the two results below are therefore the two
existence statements of the construction module, read at that spelling. The first map is the
canonical one, being the image of
`Stacks.AlgebraicGeometry.RelativeMayerVietoris.mvRes`.

The statements carry no `[HasDerivedCategory.{w}]` binder and are therefore at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The ringed-space form of the tag,
`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover`, is elaborated under a
file-level `HasDerivedCategory.standard` and derives the endofunctors `j_{W,*} j_W^*` as single
functors rather than as the composites `Rj_{W,*} ∘ j_W^*` across the open subschemes; neither
difference is a weakening of the tag, but both make that statement unusable here.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe u

namespace Stacks.Duality.Coherator

variable {X : Scheme.{u}} (U V : X.Opens)

/-- **[Stacks, Tag 08BV] for a scheme.** For opens `U`, `V` of a scheme `X` and any object `K` of
the unbounded derived category `D(𝒪_X)` there is a distinguished triangle

`Rj_{U ∪ V,*}(K|_{U ∪ V}) ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶`

in `D(𝒪_X)`, where `j_W : W → X` are the inclusions of the open subschemes.

This is `Stacks.Duality.Coherator.exists_distTriang_restrictPushforward_sup`, read in the
vocabulary of `Stacks.Duality.Coherator.IsMayerVietorisApex`. -/
@[stacks 08BV "the scheme-level form: `U`, `V` opens of a scheme inside their union, with the \
  terms `Rj_{W,*}(K|_W)` of `D(𝒪_X)` at the locally small model"]
theorem isMayerVietorisApex_restrictPushforward_sup (K : DerivedCategory X.Modules) :
    IsMayerVietorisApex X U V K (restrictPushforward (U ⊔ V) K) :=
  exists_distTriang_restrictPushforward_sup U V K

/-- **[Stacks, Tag 08BV] for a scheme, in the form of the source.** If the opens `U`, `V` cover the
scheme `X`, then every object `K` of `D(𝒪_X)` itself sits in a distinguished triangle

`K ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ K⟦1⟧`.

This is `Stacks.Duality.Coherator.exists_distTriang_self`, read in the vocabulary of
`Stacks.Duality.Coherator.IsMayerVietorisApex`. -/
@[stacks 08BV "the scheme-level form for a cover of the whole scheme, with `K` itself as the \
  first term of the triangle"]
theorem isMayerVietorisApex_self (hUV : U ⊔ V = ⊤) (K : DerivedCategory X.Modules) :
    IsMayerVietorisApex X U V K K :=
  exists_distTriang_self U V hUV K

end Stacks.Duality.Coherator

end
