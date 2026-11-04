module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.CurvePoints
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertScheme
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Geometry.HilbertSchemeGeometry
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Glue.Representable

/-!
# The Hilbert schemes of points of a curve are representable

Let `X` be a curve over a field `k` (a separated scheme of finite type, integral, of dimension
one; e.g. a smooth projective curve) with structure morphism `f : X ⟶ Spec k`. For every `d` the
Hilbert functor of degree-`d` closed subschemes `Hilb^d_{X/k}` is representable.

This is Stacks Tag 0B9A for `X ⟶ Spec k`: `Spec k` is affine, `X` is separated over it, and any
finitely many points of `X` lie in a common affine open (Stacks Tag 09NN,
`Stacks.Hilbert.hilbertHypothesis_of_isCurve`), which is the hypothesis of
`Stacks.Hilbert.isRepresentable_hilbPresheaf_of_affineOpens`. The source uses the case of a
smooth projective curve in the proof of Stacks Tag 0B9I and of Stacks Tag 0B9Z (with
`d = genus f`).

## Main results

* `Stacks.Hilbert.isRepresentable_hilbPresheaf_of_isCurve`: the Hilbert presheaf of a curve is
  representable, in every degree (an instance). With it,
  `Stacks.Hilbert.representsHilbOver (Over.mk f) d :
    RepresentsHilbertFunctorOfRank (Over.mk f) (hilbOver (Over.mk f) d) d`
  holds with no further hypothesis.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isCurve`: some `k`-scheme represents
  `Hilb^d_{X/k}`.
* `Stacks.Hilbert.hilbOver_isProper_smooth_irreducible_dim`: for `k` algebraically closed and
  `X` a smooth proper curve, `Hilb^d_{X/k}` is a proper smooth irreducible `k`-scheme of
  dimension `d`, smooth of relative dimension `d` and integral (part (1) of Stacks Tag 0B9I).

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Hilbert functor of points of a curve is representable** in every degree: Stacks
Tag 0B9A over the affine base `Spec k`, whose hypothesis is that finitely many points of a curve
lie in a common affine open (Stacks Tag 09NN). -/
instance isRepresentable_hilbPresheaf_of_isCurve [IsCurve k f] (d : ℕ) :
    (hilbPresheaf (Over.mk f) d).IsRepresentable :=
  isRepresentable_hilbPresheaf_of_affineOpens (Over.mk f) d (hilbertHypothesis_of_isCurve f d)

/-- **Some `k`-scheme represents the Hilbert functor of points of degree `d` of a curve**:
the Hilbert scheme `hilbOver (Over.mk f) d`. -/
theorem exists_representsHilbertFunctorOfRank_of_isCurve [IsCurve k f] (d : ℕ) :
    ∃ H : Over (Spec (.of k)), Nonempty (RepresentsHilbertFunctorOfRank (Over.mk f) H d) :=
  ⟨hilbOver (Over.mk f) d, ⟨representsHilbOver (Over.mk f) d⟩⟩

/-- **The Hilbert scheme of points of a smooth proper curve is a smooth proper variety of
dimension `d`** (part (1) of Stacks Tag 0B9I, for the Hilbert scheme `hilbOver (Over.mk f) d`):
for `k` algebraically closed, `Hilb^d_{X/k}` is proper over `k`, smooth of relative dimension
`d`, irreducible and integral, of dimension `d`. -/
theorem hilbOver_isProper_smooth_irreducible_dim [IsAlgClosed k] [IsCurve k f] [Smooth f]
    [IsProper f] (d : ℕ) :
    IsProper (hilbOver (Over.mk f) d).hom ∧
      SmoothOfRelativeDimension d (hilbOver (Over.mk f) d).hom ∧
      IrreducibleSpace (hilbOver (Over.mk f) d).left ∧
      IsIntegral (hilbOver (Over.mk f) d).left ∧
      topologicalKrullDim (hilbOver (Over.mk f) d).left = d :=
  hilbertScheme_isProper_smooth_irreducible_dim f (fun e => hilbOver (Over.mk f) e)
    (fun e => representsHilbOver (Over.mk f) e) d

end Stacks.Hilbert

end
