module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Varieties.Kunneth
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqs
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula for schemes with affine diagonal

Let `k` be a field and let `X` and `Y` be quasi-compact schemes over `k` whose diagonals are
affine, for instance separated schemes. For a quasi-coherent `𝒪_X`-module `F` and a
quasi-coherent `𝒪_Y`-module `G` the cohomology of the external tensor product
`pr₁^*F ⊗ pr₂^*G` on `X ×_{Spec k} Y` is the direct sum of the tensor products
`Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`.

## Main results

* `AlgebraicGeometry.nonempty_kunnethIso_of_isAffineHom_diagonal`: the Künneth formula for
  quasi-compact schemes with affine diagonal.
* `AlgebraicGeometry.nonempty_kunnethIso_of_isSeparated`: the Künneth formula for quasi-compact
  separated schemes, affineness of the diagonal being automatic there.

## Implementation notes

Affineness of the diagonal is spelled `IsAffineHom (pullback.diagonal (terminal.from X))` and
quasi-compactness is `CompactSpace`, as elsewhere in this development; a scheme with affine
diagonal is quasi-separated because an affine morphism is quasi-compact
(`AlgebraicGeometry.quasiSeparatedSpace_of_isAffineHom_diagonal`). The isomorphism is therefore
the Künneth isomorphism `AlgebraicGeometry.KunnethQcqs.kunnethIso` for quasi-compact
quasi-separated schemes, the inverse of the canonical Künneth map of [Stacks, Tag 0BEF], which
`AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap` proves invertible from the derived global
Künneth comparison of Tag 0FLQ.

*Relation to the Čech form.* `Stacks.CechKunneth.kunnethIsoOfAffineDiagonal` builds the same
decomposition as in the source, from the Čech complexes of finite affine coverings and the cup
product of Tag 07MB on the product covering; `Stacks.CechKunneth.kunnethIsoOfAffineDiagonal_eq`
shows it does not depend on the coverings.

*Isomorphisms as `Nonempty`.* The conclusions here are stated as `Nonempty (… ≅ …)`; the
explicit isomorphisms are `AlgebraicGeometry.KunnethQcqs.kunnethIso` and
`Stacks.CechKunneth.kunnethIsoOfAffineDiagonal`.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped DirectSum TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The Künneth formula.** For quasi-coherent modules `F` on `X` and `G` on `Y`, with `X` and
`Y` quasi-compact schemes over a field `k` whose diagonals are affine, the cohomology of the
external tensor product `pr₁^*F ⊗ pr₂^*G` on `X ×_{Spec k} Y` is isomorphic to the direct sum of
the tensor products `Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`. -/
@[stacks 0BED "for X and Y quasi-compact with affine diagonal over a field k and F, G \
quasi-coherent: H^n(X x_k Y, pr_1^*F (x) pr_2^*G) is isomorphic to the direct sum over \
p + q = n of H^p(X, F) (x)_k H^q(Y, G)"]
theorem nonempty_kunnethIso_of_isAffineHom_diagonal
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) :=
  ⟨KunnethQcqs.kunnethIso f g F G n⟩

/-- **The Künneth formula, I, for separated schemes.** The diagonal of a separated scheme is a
closed immersion and therefore affine, so the Künneth formula holds for quasi-coherent modules
on quasi-compact separated schemes over a field. -/
theorem nonempty_kunnethIso_of_isSeparated
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) :=
  nonempty_kunnethIso_of_isAffineHom_diagonal k f g F G n

end AlgebraicGeometry

end
