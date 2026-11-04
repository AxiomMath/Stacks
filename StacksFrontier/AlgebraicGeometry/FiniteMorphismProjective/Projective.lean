module

public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.PushforwardEmbedding
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FiniteMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite morphism is projective

[Stacks, Tag 0B3I]. A finite morphism `f : X ⟶ S` is projective: `X` is, over `S`, a closed
subscheme of the projective bundle `𝐏(f_*𝒪_X)`.

The module `f_*𝒪_X` is quasi-coherent because `f` is affine (Tag 01SA) and of finite type because
`f` is finite (Tag 01PB). The closed immersion `X ⟶ 𝐏(f_*𝒪_X) = Proj_S(Sym(f_*𝒪_X))` over `S` is
`Stacks.FiniteMorphismProjective.embedding`: over an affine open `V = Spec R` of the base with
`f⁻¹(V) = Spec A`, it is the closed immersion of `Spec A` into the standard chart `D₊(1)` of
`Proj Sym_R(A)` cut out by the surjection `Sym_R(A)_{(1)} → A`, and these local morphisms glue.

## Main results

* `Stacks.FiniteMorphismProjective.isFiniteType_structurePushforward`: `f_*𝒪_X` is of finite type
  for a finite `f`.
* `Stacks.FiniteMorphismProjective.isProjective_of_isFinite_of_isAffine`: a finite morphism over
  an affine base is projective, through the H-projective route of
  `Stacks.FiniteMorphismProjective.isHProjective_of_isFinite_of_isAffine` and Tag 01W9.
* `Stacks.FiniteMorphismProjective.isProjective_of_isFinite`: **Tag 0B3I**, a finite morphism
  over an arbitrary base is projective.

## References

* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.FiniteMorphismProjective

universe u

/-! ### Over an affine base -/

/-- **A finite morphism over an affine base is projective**, in the sense of Tag 01W8's first
condition: a closed immersion into the projective bundle of a quasi-coherent module of finite
type on the base, over the base.

The witnessing bundle is `𝐏(𝒪_S^{n+1}) = ℙⁿ_S`: over an affine base the generators of
`Γ(X, 𝒪_X)` as a `Γ(S, 𝒪_S)`-module give a closed immersion into `ℙⁿ_S`, and Tag 01OE identifies
that with a projective bundle over `S`. -/
public theorem isProjective_of_isFinite_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsFinite f] : AlgebraicGeometry.IsProjective f := by
  obtain ⟨n, i, hi, hif⟩ := isHProjective_of_isFinite_of_isAffine f
  exact AlgebraicGeometry.IsProjectiveMorphism.isProjective ⟨n, i, hi, hif⟩

/-! ### The pushforward of the structure sheaf -/

/-- **`f_*𝒪_X` is of finite type for a finite morphism.** This is Tag 01PB read through the
definition of finiteness, in the form
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_pushforward_of_isFinite`. -/
public instance isFiniteType_structurePushforward {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    (structurePushforward f).IsFiniteType :=
  Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_pushforward_of_isFinite f _

/-! ### Tag 0B3I -/

/-- **A finite morphism is projective.** For a finite `f : X ⟶ S` over an arbitrary base scheme,
`X` is, over `S`, a closed subscheme of the projective bundle `𝐏(f_*𝒪_X)` of a quasi-coherent
module of finite type.

The module is `f_*𝒪_X`, quasi-coherent by Tag 01SA and of finite type by Tag 01PB, and the closed
immersion is `Stacks.FiniteMorphismProjective.embedding`, which is a morphism over the base by
`Stacks.FiniteMorphismProjective.embedding_comp_toBase` and a closed immersion by
`Stacks.FiniteMorphismProjective.isClosedImmersion_embedding`. -/
@[stacks 0B3I, ega "II 5.5.5" "more general", ega "II 6.1.11"]
public theorem isProjective_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    AlgebraicGeometry.IsProjective f :=
  ⟨structurePushforward f, inferInstance, inferInstance,
    Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _, embedding f,
    isClosedImmersion_embedding f, embedding_comp_toBase f⟩

end Stacks.FiniteMorphismProjective

end
