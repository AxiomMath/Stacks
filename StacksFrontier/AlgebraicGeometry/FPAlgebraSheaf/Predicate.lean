module

public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra

/-!
# The two finite presentation predicates on an algebra sheaf are the same

Finite presentation of a sheaf of commutative `𝒪_X`-algebras has been stated twice in this
project, independently and in different namespaces:

* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation`, which is what the
  statement of [Stacks, Tag 05JS] and the reduction of that tag in
  `Stacks.QcohAlgebraFPColimit` are phrased with;
* `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation`, which is what the finiteness
  conditions of [Stacks, Tag 0817] and the transport lemmas alongside them are phrased with.

The two carriers `AlgebraicGeometry.Scheme.QuasicoherentAlgebra X` and
`Stacks.RelativeSpec.AlgebraSheaf X` are both reducible abbreviations for `Under X.sheaf`, so
they are the same type and a term of one is a term of the other with no coercion.  The two
predicates, however, are `def`s, so neither unfolds to the other during unification and *a
lemma about one does not apply to the other by name*.  This file closes that gap once, so that
the transport lemmas proved for `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` are
usable against the conclusion of Tag 05JS and conversely.

`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` is the canonical form:
it lives in the promoted `StacksDraft.AlgebraicGeometry.Properties` namespace, and it is the
predicate appearing in the existential that Tag 05JS has to
discharge, so a construction must ultimately produce it.  New results are therefore stated
against it, and the equivalence below is what carries them over to the other spelling.

## Main results

* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_iff_isFinitePresentation`: **the two
  independently stated finite presentation predicates on an algebra sheaf agree.**
* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_structureSheaf`: the structure sheaf, viewed as
  an algebra over itself, is of finite presentation.

## Implementation notes

The equivalence is `Iff.rfl`: both predicates are `∀ U, IsAffineOpen U → RingHom.FinitePresentation
(A.hom.hom.app (op U)).hom` verbatim, and the only thing standing between them is that a `def`
is not unfolded by `exact`.  Nothing is proved here that was not already true; what is supplied
is a name to rewrite along.

The structure sheaf is recorded because it is the one algebra sheaf whose finite presentation
needs no geometry at all -- the structural ring map is the identity at every open -- and it is
the base point of any directed system of algebras over `𝒪_X`.  It is *not* an example of a
nontrivial finitely presented algebra sheaf, and is not offered as one.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.FPAlgebraSheaf

variable {X : Scheme.{u}}

/-- **The two finite presentation predicates on an algebra sheaf agree.**
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` and
`Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` were stated independently, in different
namespaces, with the same body; this identifies them, so that a lemma about either applies to
the other. -/
theorem isOfFinitePresentation_iff_isFinitePresentation (A : X.QuasicoherentAlgebra) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation A ↔
      Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation A :=
  Iff.rfl

/-- A `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` hypothesis discharges the finite
presentation clause of [Stacks, Tag 05JS]. -/
theorem _root_.Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation.isOfFinitePresentation
    {A : X.QuasicoherentAlgebra} (hA : Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation A) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation A :=
  hA

/-- The finite presentation clause of [Stacks, Tag 05JS] is the finite presentation condition of
the finiteness file, so the transport and restriction lemmas proved there apply to it. -/
theorem
    _root_.AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation.isFinitePresentation
    {A : X.QuasicoherentAlgebra} (hA : Scheme.QuasicoherentAlgebra.IsOfFinitePresentation A) :
    Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation A :=
  hA

/-- The structure sheaf of a scheme, as an algebra over itself, is of finite presentation: at
every open the structural ring map is the identity. -/
theorem isOfFinitePresentation_structureSheaf (X : Scheme.{u}) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (Under.mk (𝟙 X.sheaf)) := by
  intro U _
  exact RingHom.FinitePresentation.id Γ(X, U)

end Stacks.FPAlgebraSheaf
