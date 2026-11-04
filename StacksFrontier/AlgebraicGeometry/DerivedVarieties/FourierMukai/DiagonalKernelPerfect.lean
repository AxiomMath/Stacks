module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal kernel of a smooth separated morphism is perfect

Let `f : X ⟶ S` be a smooth separated morphism of schemes with diagonal
`Δ = Δ_{X/S} : X ⟶ X ×_S X`. This file proves that the diagonal kernel

`𝒪_Δ = RΔ_*𝒪_X ∈ D(𝒪_{X ×_S X})`

of `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernel.lean` is a
*perfect* object, i.e. lies in `D_{perf}(𝒪_{X ×_S X})`.

This is clause (4) of the construction in Section 0G0F of the source — the clause asserting
that the candidate identity morphism of the category of Fourier-Mukai kernels is a morphism at
all — and it is assembled out of exactly the three results the source cites there:
[Stacks, Tag 067U], [Stacks, Tag 068C] and [Stacks, Tag 0G2E].

## Main results

* `AlgebraicGeometry.perfect_diagonal` — the diagonal of a smooth separated morphism is a
  perfect morphism of schemes.
* `AlgebraicGeometry.isPerfect_diagonalKernel_ringedSpace` — `𝒪_Δ = RΔ_*𝒪_X` is a perfect object of
  `D(𝒪_{X ×_S X})`.

## The source's chain, step by step

1. `Δ` is an immersion between two schemes smooth over `S`: `X ⟶ S` is smooth by hypothesis and
   `X ×_S X ⟶ S` is smooth because smoothness is stable under base change and composition. By
   [Stacks, Tag 067U] — `Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth` — it
   is therefore a regular immersion.
2. A regular immersion is a perfect morphism, [Stacks, Tag 068C], which is
   `AlgebraicGeometry.perfect_of_isRegularImmersion`.
3. The direct image of the structure sheaf along a perfect closed immersion is a perfect
   object, [Stacks, Tag 0G2E], which is
   `AlgebraicGeometry.isPerfect_pushforward_structureSheaf`. Separatedness of `f` is what makes
   `Δ` a closed immersion.

Step 3 produces perfectness of the *ordinary* direct image `Δ_*𝒪_X` placed in degree zero,
while `AlgebraicGeometry.diagonalKernel` is the *derived* direct image `RΔ_*𝒪_X`. The source
identifies the two silently when it writes `𝒪_Δ = Δ_*𝒪_X = RΔ_*𝒪_X`; the identification is
supplied here by `AlgebraicGeometry.derivedPushforwardSingleIso`, which is nothing but the fact
that pushforward along a closed immersion is exact, so that the functor it induces on derived
categories *is* its own total right derived functor. That is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, whose exactness input is
[Stacks, Tag 08KS].

## Implementation notes

*Only smooth and separated, not smooth and proper.* Section 0G0F takes `X` proper and smooth
over `S`; properness is used there for the composition law and plays no part in clause (4). The
statements below therefore ask for `[Smooth f]` and `[IsSeparated f]` only, which is a
generalisation of the clause and covers the source's case (a proper morphism is separated).

*No `@[stacks 0G0F]` attribute.* Tag 0G0F is the assertion that the category of Fourier-Mukai
kernels *exists*; this file proves one of the four clauses of its construction and does not
state the tag. The three clauses it does not touch are: that the convolution of two perfect
kernels is perfect (the perfectness half of [Stacks, Tag 0B91], at a general base, which this
library does not carry — see the attribute note at
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean:233`); associativity
of convolution (which runs on [Stacks, Tag 08IB], carried as a hypothesis throughout, see
`AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` in
`FourierMukai/Composition.lean:332`); and the unit laws, which the source itself omits.

*The two spellings of the category of modules on a scheme.*
`AlgebraicGeometry.Scheme.Modules` and `StrictlyPerfect.OXMod` of the underlying ringed space
are the same category by `rfl`, but the derived-category instance each one synthesises is not
syntactically the same term, and asking the elaborator to unify them inside
`AlgebraicGeometry.RingedSpace.IsPerfect.of_iso` is expensive. The perfectness coming out of
[Stacks, Tag 0G2E] is therefore bound to a `have` whose type is written out in the
`Scheme.Modules` spelling before the transport is applied.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernel.lean`, everything is
read at `CategoryTheory.HasDerivedCategory.standard`, given a raised local instance priority so
that the locally small model arriving with the imports does not compete.

## References

* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0G2E](https://stacks.math.columbia.edu/tag/0G2E)
* [Stacks Project, Tag 067U](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Tag 068C](https://stacks.math.columbia.edu/tag/068C)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the diagonal
-- kernel is read at, over the locally small model arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The derived direct image of a module in degree zero along a closed immersion -/

/-- **Pushforward along a closed immersion needs no derivation in degree zero**:
`Ri_*(M[0]) ≅ (i_*M)[0]` for a closed immersion of schemes `i : Z ⟶ W` and an
`𝒪_Z`-module `M`.

Pushforward along a closed immersion is exact ([Stacks, Tag 08KS]), so the functor
`i_*` induces on derived categories is a total right derived functor of itself; that comparison
is `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`. An exact functor commutes
with the single-degree functors, which is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

This is the identification the source performs silently when it writes `Δ_*𝒪_X = RΔ_*𝒪_X` in
Example 0FYV and in Section 0G0F. -/
def derivedPushforwardSingleIso {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    (M : Z.Modules) :
    (derivedPushforwardModules i).obj ((DerivedCategory.singleFunctor Z.Modules 0).obj M) ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj ((Scheme.Modules.pushforward i).obj M) :=
  ((Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom)).app _).symm ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom) 0).app M

/-! ### The diagonal of a smooth morphism is perfect -/

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- **The diagonal of a smooth separated morphism is a perfect morphism.** This is the input
Section 0G0F cites for clause (4), namely [Stacks, Tag 067U] followed by [Stacks, Tag 068C].

`Δ : X ⟶ X ×_S X` is an immersion — a closed one, `f` being separated — between two schemes
smooth over `S`: `X ×_S X ⟶ S` is `pr_1 ≫ f`, smooth because `pr_1` is a base change of the
smooth `f`, and `Δ ≫ (pr_1 ≫ f) = f` is smooth by hypothesis. So `Δ` is a regular immersion by
[Stacks, Tag 067U] and hence perfect by [Stacks, Tag 068C].

No `@[stacks]` attribute: this is an application of those two tags at one morphism, not a
clause of either statement. -/
instance perfect_diagonal [IsSeparated f] [Smooth f] : Perfect (Limits.pullback.diagonal f) := by
  have hcomp : Limits.pullback.diagonal f ≫ (Limits.pullback.fst f f ≫ f) = f := by
    rw [← Category.assoc, Limits.pullback.diagonal_fst, Category.id_comp]
  have : Smooth (Limits.pullback.diagonal f ≫ (Limits.pullback.fst f f ≫ f)) := by
    rw [hcomp]; infer_instance
  exact perfect_of_isRegularImmersion _
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth
      (Limits.pullback.diagonal f) (Limits.pullback.fst f f ≫ f))

/-! ### The diagonal kernel is perfect -/

/-- **The diagonal kernel of a smooth separated morphism is a perfect object.** For
`f : X ⟶ S` smooth and separated,

`𝒪_Δ = RΔ_{X/S,*}𝒪_X ∈ D_{perf}(𝒪_{X ×_S X})`.

This is clause (4) of the construction of Section 0G0F — the assertion that the candidate
identity morphism of `X` in the category of Fourier-Mukai kernels really is a morphism — proved
from the three results the source cites there: `Δ` is a regular immersion by
[Stacks, Tag 067U], hence a perfect morphism by [Stacks, Tag 068C], hence has perfect direct
image of the structure sheaf by [Stacks, Tag 0G2E]. The passage from the ordinary direct image
of that last tag to the derived one of `AlgebraicGeometry.diagonalKernel` is
`AlgebraicGeometry.derivedPushforwardSingleIso`.

No `@[stacks 0G0F]` attribute: Tag 0G0F is the existence of the category, and this is one of the
four clauses of its construction — see the implementation notes of this file for the three that
are missing. -/
@[sga "6 III 1.1.2" "special case"]
theorem isPerfect_diagonalKernel_ringedSpace [IsSeparated f] [Smooth f] :
    RingedSpace.IsPerfect (X := (Limits.pullback f f).toRingedSpace) (diagonalKernel f) := by
  have h : RingedSpace.IsPerfect (X := (Limits.pullback f f).toRingedSpace)
      ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
        ((Scheme.Modules.pushforward (Limits.pullback.diagonal f)).obj
          (SheafOfModules.unit X.ringCatSheaf))) :=
    isPerfect_pushforward_structureSheaf (Limits.pullback.diagonal f)
  exact h.of_iso
    (derivedPushforwardSingleIso (Limits.pullback.diagonal f)
      (SheafOfModules.unit X.ringCatSheaf)).symm

end AlgebraicGeometry

end
