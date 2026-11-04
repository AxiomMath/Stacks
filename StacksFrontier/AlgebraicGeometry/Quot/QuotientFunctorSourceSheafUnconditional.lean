module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientDescentClauses
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSourceSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageLocalPresentations
import StacksCore.Tactic.StacksAttribute

/-!
# The functor of quotients is an fpqc sheaf in the source (Stacks 08IV)

In Situation 082M — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` together with
a quasi-coherent `𝒪_X`-module `F` — let `{X i ⟶ X}` be an fpqc covering and for each pair `i, j`
let `{X ijk ⟶ X i ×_X X j}` be an fpqc covering.  Stacks 08IV asserts that for every scheme `T`
over `Y` the diagram

`Q_{F/X/Y}(T) ⟶ ∏_i Q_{F i/X i/Y}(T) ⇉ ∏_{ijk} Q_{F ijk/X ijk/Y}(T)`

presents the first arrow as the equalizer of the other two, and that the same is true for
`Q^{fp}_{F/X/Y}`.

Both statements are proved as bijections onto the matching families, with no hypothesis beyond
Situation 082M and the two coverings, by
`AlgebraicGeometry.Space.QuotientSituation.bijOn_restrictQuotientToMember` and its
finite-presentation companion of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSourceSheaf.lean`.  This file is the two names
under which the fpqc-covering reading of Stacks 08IV refers to them, and nothing else: every
result it used to prove separately is now stated there, where no hypothesis is left to carry.

## Main results

* `QuotientSituation.bijOn_restrictQuotientToMember_of_isFpqcCovering`: **Stacks 08IV** for
  `Q_{F/X/Y}`.
* `QuotientSituation.bijOn_restrictQuotientToMember_finitePresentation_of_isFpqcCovering`:
  **Stacks 08IV** for `Q^{fp}_{F/X/Y}` (with Stacks 060V).

## References

* [Stacks Project, Tag 08IV](https://stacks.math.columbia.edu/tag/08IV)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Stacks 08IV -/

/-- In Situation 082M, let `{a i : W i ⟶ X}` be an fpqc covering of the source, let `P i j` be the
fibre product `W i ×_X W j` and let `{Z i j k ⟶ P i j}` be fpqc coverings. For every scheme `T`
over `Y` the diagram

`Q_{F/X/Y}(T) ⟶ ∏_i Q_{F i/W i/Y}(T) ⇉ ∏_{ijk} Q_{F ijk/Z i j k/Y}(T)`

presents the first arrow as the equalizer of the other two: restriction is a bijection from
`Q_{F/X/Y}(T)` onto the set of families `(Q i)` of elements of the `Q_{F i/W i/Y}(T)` whose two
restrictions `pr₀^*`, `pr₁^*` to each `Z i j k` agree.  Being a bijection onto that set is the
commutativity `pr₀^* ∘ res = pr₁^* ∘ res`, the injectivity of `res`, and the surjectivity of
`res` onto the equalizer.

Here `F i` is the inverse image of `F` along `a i` and `F ijk` the inverse image of `F` along the
single morphism `e i j k : Z i j k ⟶ X`. -/
@[stacks 08IV]
alias bijOn_restrictQuotientToMember_of_isFpqcCovering :=
  bijOn_restrictQuotientToMember

/-- The diagram of Stacks 08IV presents the first arrow as the equalizer of the other two for
`Q^{fp}_{F/X/Y}` as well: restriction is a bijection from `Q^{fp}_{F/X/Y}(T)` onto the set of
families of elements of the `Q^{fp}_{F i/W i/Y}(T)` whose two restrictions to each `Z i j k`
agree. -/
@[stacks 08IV]
alias bijOn_restrictQuotientToMember_finitePresentation_of_isFpqcCovering :=
  bijOn_restrictQuotientToMember_finitePresentation

end QuotientSituation

end AlgebraicGeometry.Space

end
