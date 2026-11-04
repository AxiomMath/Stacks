module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Varieties.Kunneth
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula for schemes with affine diagonal

Let `k` be a field and let `X` and `Y` be quasi-compact schemes over `k` whose diagonals are
affine, for instance separated schemes. For a quasi-coherent `𝒪_X`-module `F` and a
quasi-coherent `𝒪_Y`-module `G` the cohomology of the external tensor product
`pr₁^*F ⊗ pr₂^*G` on `X ×_{Spec k} Y` is the direct sum of the tensor products
`Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`.

## Main definitions

* `AlgebraicGeometry.HasKunnethDerivedData`: the derived global Künneth comparison of Tag 0FLQ,
  as a statement about every quasi-compact scheme with affine diagonal over a field and every
  quasi-coherent module on it.

## Main results

* `AlgebraicGeometry.nonempty_kunnethIso_of_isAffineHom_diagonal`: the Künneth formula for
  quasi-compact schemes with affine diagonal.
* `AlgebraicGeometry.nonempty_kunnethIso_of_isSeparated`: the Künneth formula for quasi-compact
  separated schemes, affineness of the diagonal being automatic there.

## Implementation notes

Affineness of the diagonal is spelled `IsAffineHom (pullback.diagonal (terminal.from X))` and
quasi-compactness is `CompactSpace`, as elsewhere in this development; a scheme with affine
diagonal is quasi-separated because an affine morphism is quasi-compact, which is how the
hypotheses of Tag 0BEF are met.

*The one carried hypothesis.* `HasKunnethDerivedData` carries the conclusion of Tag 0FLQ:
that the derived global sections of the external tensor product are the derived tensor product
over `k` of the derived global sections of the two factors. It is quantified over all of its own
data — every field, every pair of quasi-compact schemes with affine diagonal over it and every
pair of quasi-coherent modules — and mentions none of the particular objects of the theorems
below. It does *not* contain the Künneth decomposition in any degree: the splitting of the
derived tensor product into the sum over `p + q = n` is proved, with no hypothesis, in
`StacksFrontier.AlgebraicGeometry.Varieties.Kunneth`, where it comes from K-flatness of every
complex of `k`-vector spaces and from the fact that such a complex is quasi-isomorphic to its
own cohomology with zero differentials. The source obtains the same comparison from the Čech
construction: the covering of `X ×_{Spec k} Y` by the products of the members of affine open
coverings of the two factors refines both pullback coverings, and the cup product of Tag 07MB
maps the total complex of the tensor product of the two Čech complexes to the Čech complex of
the product. Assembling that map needs the sections of the external tensor product over a
product of affine opens, which this development does not describe, so the comparison is carried
rather than built.

*Isomorphisms as `Nonempty`.* The conclusion is `Nonempty (… ≅ …)` rather than a constructed
comparison map proved invertible. The isomorphism of Tag 0BEF is produced from a choice of
basis of each cohomology module, and no cup product on the sheaf cohomology of a scheme is
available to write down the canonical map of the source, which is a pullback followed by a cup
product.

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

/-- The derived global Künneth comparison of Tag 0FLQ, for every quasi-compact scheme with
affine diagonal over a field: complexes of `k`-vector spaces computing `RΓ(X, F)` and
`RΓ(Y, G)` whose derived tensor product computes `RΓ(X ×_{Spec k} Y, pr₁^*F ⊗ pr₂^*G)`. -/
def HasKunnethDerivedData : Prop :=
  ∀ (k : Type u) [Field k] (X Y : Scheme.{u}) (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)),
    CompactSpace X → CompactSpace Y →
    IsAffineHom (pullback.diagonal (terminal.from X)) →
    IsAffineHom (pullback.diagonal (terminal.from Y)) →
    ∀ (F : X.Modules) (G : Y.Modules), F.IsQuasicoherent → G.IsQuasicoherent →
      Nonempty (KunnethDerivedData k f g F G)

/-- **The Künneth formula, I.** For quasi-coherent modules `F` on `X` and `G` on `Y`, with `X`
and `Y` quasi-compact schemes over a field `k` whose diagonals are affine, the cohomology of
the external tensor product `pr₁^*F ⊗ pr₂^*G` on `X ×_{Spec k} Y` is the direct sum of the
tensor products `Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`. -/
@[stacks 0BED "granted the derived global Künneth comparison of Tag 0FLQ, carried as \
HasKunnethDerivedData"]
theorem nonempty_kunnethIso_of_isAffineHom_diagonal
    (hK : HasKunnethDerivedData.{u}) (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) := by
  obtain ⟨d⟩ := hK k X Y f g ‹_› ‹_› ‹_› ‹_› F G ‹_› ‹_›
  exact nonempty_kunnethIso k f g F G n d

/-- **The Künneth formula, I, for separated schemes.** The diagonal of a separated scheme is a
closed immersion and therefore affine, so the Künneth formula holds for quasi-coherent modules
on quasi-compact separated schemes over a field. -/
theorem nonempty_kunnethIso_of_isSeparated
    (hK : HasKunnethDerivedData.{u}) (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) :=
  nonempty_kunnethIso_of_isAffineHom_diagonal hK k f g F G n

end AlgebraicGeometry

end
