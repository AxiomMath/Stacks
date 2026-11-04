module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepFull
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction

/-!
# Absolute Noetherian approximation relative to a quasi-compact open

Let `S` be a quasi-compact quasi-separated scheme and let `U ⊆ S` be a quasi-compact open which is
the inverse limit of an inverse system of schemes of finite type over the integers with affine
transition morphisms.  Then `S` itself is such an inverse limit, compatibly: there is an inverse
system `S_j` of schemes of finite type over the integers with affine transition morphisms, open
subschemes `V_j ⊆ S_j` pulling back to one another, and a reindexing of the given system, such
that `S = lim S_j` and `U = lim V_j`.

The statement is obtained from its single-affine case by induction on a finite affine cover of the
complement of the open, which is
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIsOneAffineOpenStep`.  The single-affine case
itself, the predicate
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`, is discharged here from
`AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine`, which proves the same extension
for a quasi-separated ambient scheme, without assuming it quasi-compact: compactness of the
ambient scheme is not used in the single-affine case, since `S = U ∪ A` for a quasi-compact `U`
and an affine `A` is quasi-compact anyway.

## Main results

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep`: **the single-affine case
  of absolute Noetherian approximation.**
* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.nonempty_of_isLimit`: **absolute Noetherian
  approximation relative to a quasi-compact open**, and
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIsLimit`, the same as data.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

section Step

/-- **The single-affine case of absolute Noetherian approximation.**  A quasi-compact
quasi-separated scheme which is the union of a quasi-compact open `U` with one affine open extends
an inverse system of finite type over the integers on `U`, with affine transition morphisms, to
such a system on the whole scheme, cofinally. -/
theorem isOneAffineOpenStep : IsOneAffineOpenStep.{u} :=
  fun D _ _ _ _ _ _ U A _ hA hcovUA p hp =>
    exists_finiteTypeApproximation_of_sup_affine D U A hA hcovUA p hp

end Step

section Relative

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵈ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
  [∀ i, QuasiCompact (terminal.from (D.obj i))]

/-- **Absolute Noetherian approximation relative to a quasi-compact open.**  Let `S` be a
quasi-compact quasi-separated scheme, let `U ⊆ S` be a quasi-compact open, and let `U` be the
inverse limit of an inverse system over a directed set with affine transition morphisms and with
every stage of finite type over the integers.  Then there are a directed set `J`, an inverse
system `(S_j)` over `J` with affine transition morphisms and every stage of finite type over the
integers, an order-preserving reindexing `J → I`, and open subschemes `V_j ⊆ S_j` pulling back to
one another along the transition morphisms and isomorphic to the corresponding stages of the
given system, such that `S = lim S_j` and `U = lim V_j` compatibly. -/
theorem nonempty_of_isLimit (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    Nonempty (FiniteTypeApproximation D S U p) :=
  exists_of_isOneAffineOpenStep D isOneAffineOpenStep S U p hp

/-- The approximation of `AlgebraicGeometry.Scheme.FiniteTypeApproximation.nonempty_of_isLimit`,
as data. -/
noncomputable def ofIsLimit (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    FiniteTypeApproximation D S U p :=
  ofIsOneAffineOpenStep D isOneAffineOpenStep S U p hp

end Relative

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

end
