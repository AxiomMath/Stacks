module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep

/-!
# Noetherian approximation relative to a quasi-compact open

Let `S` be a quasi-compact quasi-separated scheme and let `U ⊆ S` be a quasi-compact open which
is the inverse limit of a directed system of schemes of finite type over the integers with affine
transition morphisms.  Then that system extends to such a system approximating `S`, compatibly
with the given one on `U`.  This is Tag 07RN, stated here both propositionally and as data.

## Main results

* `AlgebraicGeometry.exists_finiteTypeApproximation`: Tag 07RN, propositional form.
* `AlgebraicGeometry.finiteTypeApproximationOfIsLimit`: Tag 07RN, the extended system itself.

## Implementation notes

Both results come from `AlgebraicGeometry.Scheme.FiniteTypeApproximation.nonempty_of_isLimit`,
which runs the induction that adds the finitely many affine opens of a cover one at a time, the
single-affine case being `AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine`.

There is one scheme universe; the index preorder lives in it, as
`AlgebraicGeometry.Scheme.FiniteTypeApproximation` requires of its index type.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

/-- **Stacks Project, Tag 07RN.**  Let `S` be a quasi-compact and quasi-separated scheme and let
`U` be a quasi-compact open subscheme which is the inverse limit of a directed system `D` of
schemes of finite type over the integers with affine transition morphisms.  Then that system
extends to such a system approximating `S`, compatibly with `D` on `U`. -/
theorem exists_finiteTypeApproximation {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens)
    [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    Nonempty (Scheme.FiniteTypeApproximation D S U p) :=
  Scheme.FiniteTypeApproximation.nonempty_of_isLimit D S U p hp

/-- **Stacks Project, Tag 07RN**, as data: the extended system itself.
It is `AlgebraicGeometry.exists_finiteTypeApproximation` together with the choice of a witness,
so it is noncomputable; the construction is propositional throughout, every stage of it being
chosen from an existential statement. -/
@[stacks 07RN]
noncomputable def finiteTypeApproximationOfIsLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens)
    [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    Scheme.FiniteTypeApproximation D S U p :=
  (exists_finiteTypeApproximation D S U p hp).some

end AlgebraicGeometry
