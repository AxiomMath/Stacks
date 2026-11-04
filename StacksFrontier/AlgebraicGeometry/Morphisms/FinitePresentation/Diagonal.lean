module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Diagonals of morphisms locally of finite type

The diagonal of a morphism of schemes which is locally of finite type is locally of finite
presentation. If the original morphism is also quasi-separated, its diagonal is of finite
presentation.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_diagonal` gives the local
  finite-presentation property of the diagonal.
* `AlgebraicGeometry.finitePresentation_diagonal` gives finite presentation of the diagonal
  when the original morphism is quasi-separated.

## Implementation notes

The two conclusions of the source lemma are stated separately. The diagonal is Mathlib's
`CategoryTheory.Limits.pullback.diagonal`. The local assertion is the descent of local finite
presentation along the composite of the diagonal with the first projection, which is the
identity.

## References

* [The Stacks Project, Tag 0818](https://stacks.math.columbia.edu/tag/0818)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

/-- The diagonal of a morphism locally of finite type is locally of finite presentation. -/
@[stacks 0818 "local finite-presentation assertion",
  ega "IV 17.4.1.2" "Delta loc. of fin. pres.",
  ega "IV 1.4.3.1"]
lemma locallyOfFinitePresentation_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] : LocallyOfFinitePresentation (pullback.diagonal f) :=
  @locallyOfFinitePresentation_of_comp _ _ _ (pullback.diagonal f) (pullback.fst f f)
    (by simpa using (inferInstance : LocallyOfFinitePresentation (𝟙 X))) inferInstance

/-- The diagonal of a quasi-separated morphism locally of finite type is of finite
presentation. -/
@[stacks 0818 "finite-presentation assertion",
  ega "IV 1.4.3.1" "special case",
  ega "IV 17.4.1.2" "special case"]
lemma finitePresentation_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] :
    AlgebraicGeometry.FinitePresentation (pullback.diagonal f) :=
  ⟨locallyOfFinitePresentation_diagonal f, inferInstance, inferInstance⟩

end AlgebraicGeometry
