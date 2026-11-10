module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-coherent module on a quasi-compact open subscheme extends to the whole scheme

Let `j : U ⟶ X` be a quasi-compact open immersion of schemes and let `G` be a quasi-coherent
module on `U`. Then `j_*G` is a quasi-coherent module on `X` whose restriction along `j` is
isomorphic to `G`, so every quasi-coherent module on `U` is the restriction of one on `X`.

Both halves of this are already available: an open immersion is separated, hence quasi-separated,
so pushforward along `j` preserves quasi-coherence by Stacks 01LC; and the counit
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` of the adjunction between
restriction and pushforward along an open immersion is an isomorphism, which identifies
`(j_*G)|_U` with `G`.

## Main results

* `AlgebraicGeometry.exists_quasicoherent_restrict_iso` — a quasi-coherent module on the source of
  a quasi-compact open immersion is, up to isomorphism, the restriction of a quasi-coherent module
  on the target.

## Implementation notes

The extension is produced up to an isomorphism of modules after restriction rather than as an
equality of subsheaves of a common ambient module; the two refinements of this statement that do
keep track of an ambient module are
`AlgebraicGeometry.exists_quasicoherent_extension`, which extends a morphism to the restriction of
a quasi-coherent module on `X`, and `AlgebraicGeometry.exists_quasicoherentSubobject_restrict`,
which extends a quasi-coherent submodule of such a restriction. Those are the other two assertions
of the same source lemma and are proved in
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/QuasiCoherentExtension.lean` by a graph
kernel
construction; neither of them implies the statement here without a quasi-coherent module on `X` to
map into, and the pushforward supplies the extension directly.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01PE.** A quasi-coherent module on a quasi-compact open subscheme
extends to a quasi-coherent module on the ambient scheme: the pushforward along the open immersion
is quasi-coherent, and its restriction is isomorphic to the given module. -/
@[stacks 01PE "extend_quasicoherent", ega "I 1.4.2"]
public lemma exists_quasicoherent_restrict_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (G : U.Modules) [G.IsQuasicoherent] :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent), Nonempty (F.restrict j ≅ G) :=
  ⟨(pushforward j).obj G, inferInstance, ⟨(restrictFunctorAdjCounitIso j).app G⟩⟩

end AlgebraicGeometry

end
