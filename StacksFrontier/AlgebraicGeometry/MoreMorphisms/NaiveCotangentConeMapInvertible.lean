module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.NaiveCotangentImmersionShift
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangle
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentPullbackFormallySmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentConeHomologyZero
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map to the shifted cone is invertible, and the triangle it produces

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space.  The
canonical map

`c : NL_{B/A} ⊗_B C ⟶ C(NL_{C/A} ⟶ NL_{C/B})[-1]`

of [Stacks Project, Tag 0E1Y] is an isomorphism on degree `0` cohomology sheaves and an
epimorphism on degree `-1` cohomology sheaves, both unconditionally.  This file observes that
those two facts, together with the extent of the three complexes, make `c` a
**quasi-isomorphism** as soon as the single sheaf `H^{-1}(NL_{B/A} ⊗_B C)` vanishes, and draws
the consequences for a morphism of schemes factored through an immersion into a formally smooth
scheme.

For `i : X ⟶ P` an arbitrary morphism of schemes and `g : P ⟶ Y` formally smooth that vanishing
is the pullback step of [Stacks Project, Tag 0FV4], which
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentPullbackFormallySmooth` proves.  So
the canonical map `i^*NL_{P/Y} ⟶ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` of [Stacks Project, Tag 0E1Z] is
invertible in `D(𝒪_X)`, which replaces the first vertex of the distinguished triangle of
[Stacks Project, Tag 0FV3] by `i^*NL_{P/Y}` and yields the distinguished triangle

`i^*NL_{P/Y} ⟶ NL_{X/Y} ⟶ NL_{X/P} ⟶ i^*NL_{P/Y}[1]`

of `D(𝒪_X)`.  Rotating it backwards and reading `NL_{X/P}` through `𝒞_{X/P}[1]` of
[Stacks Project, Tag 0FV2] and `i^*NL_{P/Y}` through `i^*Ω_{P/Y}[0]` exhibits `NL_{X/Y}` as the
cone of a map from the conormal sheaf, placed in degree `-1`, to the pulled-back relative
differentials, placed in degree `0`.

## Main definitions

* `Stacks.NaiveCotangentConeInvertible.coneMapIso`: the isomorphism
  `i^*NL_{P/Y} ≅ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` of `D(𝒪_X)`.
* `Stacks.NaiveCotangentConeInvertible.cotangentTriangle`: the triangle
  `i^*NL_{P/Y} ⟶ NL_{X/Y} ⟶ NL_{X/P} ⟶ i^*NL_{P/Y}[1]`.
* `Stacks.NaiveCotangentConeInvertible.derivedConormalShiftIso` and
  `...derivedPullbackDifferentialsIso`: the two identifications
  `𝒞_{X/P}[1] ≅ NL_{X/P}` and `i^*NL_{P/Y} ≅ i^*Ω_{P/Y}[0]` of `D(𝒪_X)`, read off the
  quasi-isomorphisms of [Stacks Project, Tag 0FV2] and of the pullback step.
* `Stacks.NaiveCotangentConeInvertible.conormalDifferentialsTriangle`: the rotated triangle with
  those three vertices rewritten,
  `𝒞_{X/P}[1][-1] ⟶ i^*Ω_{P/Y}[0] ⟶ NL_{X/Y} ⟶ 𝒞_{X/P}[1]`.

## Main results

* `Stacks.SheafOfModules.quasiIso_spaceNaiveCotangentConeMap`: the canonical map of
  [Stacks Project, Tag 0E1Y] is a quasi-isomorphism once `H^{-1}` of its source vanishes, and
  `Stacks.SheafOfModules.quasiIso_ringedSpaceNaiveCotangentConeMap` the same for a pair of
  composable morphisms of ringed spaces.
* `Stacks.NaiveCotangentConeInvertible.quasiIso_coneMap` and `...isIso_Q_map_coneMap`: for `g`
  formally smooth the canonical map of [Stacks Project, Tag 0E1Z] is a quasi-isomorphism, hence
  invertible in `D(𝒪_X)`.
* `Stacks.NaiveCotangentConeInvertible.cotangentTriangle_distinguished` and
  `...invRotate_cotangentTriangle_distinguished`.
* `Stacks.NaiveCotangentConeInvertible.conormalDifferentialsTriangle_distinguished`: the rotated
  triangle is distinguished, so `NL_{X/Y}` is the cone of a map from the conormal sheaf in
  degree `-1` to `i^*Ω_{P/Y}` in degree `0`.

## Route

A chain map of complexes of sheaves is a quasi-isomorphism exactly when it induces an
isomorphism on cohomology sheaves in every degree, so the work is degreewise.

* Degree `0` is `Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`,
  already available.
* Degree `-1` is `Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`,
  already available, together with the hypothesis: an epimorphism whose source is a zero object
  has a zero target, and a morphism between zero objects is an isomorphism.
* In every other degree both sides vanish.  The source is the termwise extension of scalars of
  `NL_{B/A}`, which has no terms outside degrees `-1` and `0`.  For the shifted cone the
  long exact sequence of the cone is used twice: the segment
  `H^{n-1}(NL_{C/B}) --∂--> Hⁿ(C(g)[-1]) ⟶ Hⁿ(NL_{C/A})`
  is exact, its right-hand term vanishes for `n ∉ {-1, 0}`, and its left-hand map vanishes —
  for `n ∉ {0, 1}` because `H^{n-1}(NL_{C/B})` is a zero object, and for `n = 1` because
  `H⁰(NL_{C/A}) ⟶ H⁰(NL_{C/B})` is an epimorphism
  (`Stacks.SheafOfModules.epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero`, the final
  `⟶ 0` of the six-term sequence) and composes with `∂` to zero.  A monomorphism into a zero
  object has a zero source.

The vanishing hypothesis is discharged for schemes by
`isZero_homology_negOne_modulePullbackNaiveCotangentComplex` in the namespace
`Stacks.NaiveCotangentPullbackFormallySmooth`, which is stated at the termwise-pullback model of
`i^*NL_{P/Y}`, carried to the inverse-image-then-extend-scalars model the canonical map is stated
at by `Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso`.

The three triangles are produced from the distinguished triangle of
[Stacks Project, Tag 0FV3] by `Stacks.NaiveCotangentConeInvertible.distTriang_mk_of_iso_obj₁`
and `...distTriang_mk_of_iso`, which replace vertices of a distinguished triangle by isomorphic
objects; both are proved in an abstract pretriangulated category, where no spelling of the
category of sheaves of `𝒪_X`-modules intervenes.

## Implementation notes

The invertibility statements are phrased as `IsIso` of a `HomologicalComplex.homologyMap` and
never name the cohomology sheaf of the shifted cone: that object is a `homology` of a
`shiftFunctor` applied to a `mappingCone`, and writing it out leaves the sheaf of rings as a
metavariable which instance search for `HasHomology` then cannot resolve.  The helper
`Stacks.NaiveCotangentConeInvertible.isIso_of_isZero_of_mono` takes the monomorphism out of that
object as an argument precisely so that its source is inferred rather than written.

For the same family of reasons the two identifications of `D(𝒪_X)` read off the
quasi-isomorphisms are built with `asIso` applied to an **explicitly supplied** `IsIso`
argument.  Instance search does not find those `IsIso` facts: the pullback step is stated at
`AlgebraicGeometry.Scheme.Modules` and the triangle lives at the spelling
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf _)` that the naive cotangent complex
of a morphism of ringed spaces is built in, and an instance registered at one of the two is
invisible to search at the other.

## Scope

[Stacks Project, Tag 0FV4] asserts a canonical isomorphism
`NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in `D(𝒪_X)`, the two-term complex on the right being
`Stacks.ConormalSequenceRight.conormalDifferentialComplex`, whose differential is the first
arrow of the conormal sequence of [Stacks Project, Tag 01UZ],
`Stacks.ConormalSequenceRight.conormalDifferential`.  **That tag is not proved here and no
attribute for it is attached.**

What is proved is the pair of steps the source's proof performs after `NL_{P/Y} = Ω_{P/Y}` and
`NL_{X/P} = 𝒞_{X/P}[1]`: the canonical map of [Stacks Project, Tag 0E1Z] is invertible, and the
resulting triangle, rotated, exhibits `NL_{X/Y}` as the cone of a map
`𝒞_{X/P} ⟶ i^*Ω_{P/Y}` in `D(𝒪_X)`.

What is **missing** is the comparison of the first morphism of that triangle with the conormal
differential.  Both of its first two vertices are images of complexes concentrated in degree
`0`, and `DerivedCategory.singleFunctor` is fully faithful, so that morphism corresponds to a
morphism of sheaves `φ : 𝒞_{X/P} ⟶ i^*Ω_{P/Y}`: the connecting morphism of the six-term
sequence of [Stacks Project, Tag 0E44] read through the degree `-1` identification of
[Stacks Project, Tag 0FV2], which in the coordinates of this library is
`Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf` followed by
`Stacks.NaiveCotangentSixTermSequence.connectingDifferentials`, up to sign.  The cone of `φ` is
the two-term complex of `φ`, so the tag follows as soon as `φ` is identified with
`Stacks.ConormalSequenceRight.conormalDifferential i g` up to sign — or, more weakly, as soon as
the two are related by automorphisms of `𝒞_{X/P}` and of `i^*Ω_{P/Y}`, which is all the cone
sees.  Nothing of that follows from further manipulation of triangles: a distinguished triangle
pins `φ` only up to those automorphisms, so `φ` has to be computed.  What the source leaves
implicit in the last line of its proof — "which, given the computations above, is equivalent to
the asserted statement" — is exactly this comparison.  The two sides are known to have the same
image in `i^*Ω_{P/Y}`, namely the kernel of the canonical map onto `Ω_{X/Y}` — for `φ` by
`Stacks.NaiveCotangentSixTermSequence.exact_sixTerm_zero_pullback` and for the conormal
differential by `Stacks.ConormalSequenceRight.conormalShortComplex_exact` — and that does not
determine either of them.

**The connecting morphism has since been computed, and the answer is minus the conormal
differential.**  `Stacks.SheafOfModules.stalk_connecting_cotangent_mk` says that for a tower
`A ⟶ B ⟶ C` of sheaves of rings on a space and a germ `f` of `B` in the kernel of `B ⟶ C`, the
connecting morphism of the six-term sequence of [Stacks Project, Tag 0E1Y] carries the class of
the cycle `[f]` of `NL_{C/B}` to the class of `-(1 ⊗ d[f])`, which is `-(1 ⊗ d f)` in
`C ⊗_B Ω_{B/A}` (`NaiveCotangent.toKaehler_baseChange_neg_basis`).  The sign is minus.  Two steps
produce it: `CochainComplex.mappingCone.cycle_connecting_apply`, which discharges the cone, the
shift and the inverse of `H⁰` of the canonical map and leaves a zig-zag, and
`NaiveCotangent.cotangent_mk_C_eq_towerNullHomotopy_add`, which is that zig-zag on a conormal
class at the ring level.  Passing from that tower to `i` and `g` costs nothing further in sign:
the scheme-level connecting morphism differs from the one above only by `H⁰` of
`Stacks.SheafOfModules.pulledNaiveCotangentComparison`, an isomorphism of complexes.

What is **still missing** is two coordinate changes, each of the shape "a known comparison
isomorphism, read at a stalk", and neither is in the library:

* the stalk of `Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf`, the degree `-1`
  identification of [Stacks Project, Tag 0FV2], read against
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` — that it carries a conormal germ
  `[f]` to the class of the constant polynomial `f` of the canonical presentation, which is the
  hypothesis `hξ` of `Stacks.SheafOfModules.stalk_connecting_cotangent_mk`.  Of its three
  factors the third is already available: the stalk of `conormalComparison`, which underlies
  `Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf`, is
  `Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv_stalkMap`.  What is absent is the stalk of
  the other two, `homologyMap (immersionTrivialComparison i) (-1)` and
  `Stacks.Conormal.Sites.trivialHomologyNegOneIso`;
* the stalk of `Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso` after
  `CochainComplex.toHomologyZero`, read against
  `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivZero` and
  `Algebra.Extension.toKaehler`.  Only the degree `0` *term* is identified at a stalk; `H⁰` of
  the base-changed complex is nowhere identified with `C_z ⊗ Ω`, it is only ever handled as a
  cokernel of those terms.  Needed with it is the stalk of
  `Stacks.ConormalSequenceRight.conormalDifferential` as
  `KaehlerDifferential.kerCotangentToTensor`, which occurs only inside proofs, in
  `StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact`, and is not a
  declaration — its sites-level analogue
  `Stacks.Sheafify.TensorDifferentialsSheafStalk.conormalSequenceStalkMapF_toCotangent` is.

With those two, equality of morphisms of sheaves of modules being stalkwise would give
`φ = -Stacks.ConormalSequenceRight.conormalDifferential i g` and the tag would follow along this
route.  **Those two coordinate changes are still missing, and this route is still unexecuted.**

[Stacks Project, Tag 0FV4] is nevertheless proved, by a different route that never forms the
triangle and so has no sign to track:
`Stacks.NaiveCotangentImmersionFormallySmooth.naiveCotangentIsoConormalDifferentialComplex`.
There the comparison is a chain map, not a morphism of `D(𝒪_X)` recovered from a triangle: the
presentation `i^{-1}𝒪_P ⟶ 𝒪_X` of `𝒪_X` over `f^{-1}𝒪_Y` has the tag's right-hand side as the
two-term complex of its conormal sequence, and it is compared with the canonical presentation
through the polynomial presentation on the sections of `i^{-1}𝒪_P`, which maps to `i^{-1}𝒪_P`
with no choices.  Nothing of the triangle of this file is used there.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map to
  the shifted cone for a tower of sheaves of rings on a space.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the same for a pair of
  composable morphisms of ringed spaces.
* [Stacks Project, Tag 0FV3](https://stacks.math.columbia.edu/tag/0FV3), the distinguished
  triangle on the canonical map `NL_{X/Y} ⟶ NL_{X/P}`.
* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2), `NL_{X/P} = 𝒞_{X/P}[1]`
  for an immersion.
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44), the six-term exact
  sequence of cohomology sheaves.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow is the differential of the two-term complex of the tag.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.NaiveCotangentConeInvertible

/-! ### Zero objects -/

section Abstract

variable {D : Type*} [Category D] [HasZeroMorphisms D]

/-- A monomorphism into a zero object has a zero source. -/
theorem isZero_of_mono_of_isZero {S T : D} (g : S ⟶ T) [Mono g] (h : IsZero T) : IsZero S :=
  IsZero.of_mono g h

/-- A morphism between zero objects is an isomorphism. -/
theorem isIso_of_isZero_of_isZero {S T : D} (f : S ⟶ T) (hS : IsZero S) (hT : IsZero T) :
    IsIso f :=
  ⟨0, by rw [comp_zero]; exact hS.eq_of_src _ _, by rw [zero_comp]; exact hT.eq_of_src _ _⟩

/-- An epimorphism out of a zero object is an isomorphism. -/
theorem isIso_of_isZero_of_epi {S T : D} (f : S ⟶ T) [Epi f] (hS : IsZero S) : IsIso f :=
  isIso_of_isZero_of_isZero f hS (IsZero.of_epi f hS)

/-- A morphism whose source is a zero object and which is followed by a monomorphism into a
zero object is an isomorphism: the monomorphism forces its target to be a zero object too. -/
theorem isIso_of_isZero_of_mono {S T U : D} (f : S ⟶ T) (g : T ⟶ U) [Mono g] (hS : IsZero S)
    (hU : IsZero U) : IsIso f :=
  isIso_of_isZero_of_isZero f hS (isZero_of_mono_of_isZero g hU)

end Abstract

/-! ### Replacing the first vertex of a distinguished triangle -/

section AbstractTriangle

open CategoryTheory.Pretriangulated

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- The first vertex of a distinguished triangle may be replaced by an isomorphic object: the
triangle obtained by precomposing the first morphism with the isomorphism and postcomposing the
third with the shift of its inverse is again distinguished. -/
theorem distTriang_mk_of_iso_obj₁ (S : Triangle D) (hS : S ∈ distTriang D) {A : D}
    (e : A ≅ S.obj₁) :
    Triangle.mk (e.hom ≫ S.mor₁) S.mor₂ (S.mor₃ ≫ e.inv⟦(1 : ℤ)⟧') ∈ distTriang D :=
  isomorphic_distinguished _ hS _
    (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [← Functor.map_comp]))

/-- All three vertices of a distinguished triangle may be replaced by isomorphic objects. -/
theorem distTriang_mk_of_iso (S : Triangle D) (hS : S ∈ distTriang D) {A B C : D}
    (e₁ : A ≅ S.obj₁) (e₂ : B ≅ S.obj₂) (e₃ : C ≅ S.obj₃) :
    Triangle.mk (e₁.hom ≫ S.mor₁ ≫ e₂.inv) (e₂.hom ≫ S.mor₂ ≫ e₃.inv)
      (e₃.hom ≫ S.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧') ∈ distTriang D :=
  isomorphic_distinguished _ hS _
    (Triangle.isoMk _ _ e₁ e₂ e₃ (by simp) (by simp)
      (by simp [← Functor.map_comp]))

end AbstractTriangle

end Stacks.NaiveCotangentConeInvertible

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (inverseImageRingHom)
open Stacks.NaiveCotangentConeInvertible

section Space

variable {T : TopCat.{u}} (A B C : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- Outside degrees `-1` and `0` the cohomology sheaves of `NL_{B/A} ⊗_B C` vanish: the complex
has no terms there, extension of scalars preserving zero objects. -/
theorem isZero_homology_spaceBaseChangeNaiveCotangentComplex (n : ℤ) (hneg : n ≠ -1)
    (hzero : n ≠ 0) :
    IsZero ((spaceBaseChangeNaiveCotangentComplex A B C a b).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (CategoryTheory.Functor.map_isZero
    (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b)
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A B a n hneg
      hzero))).isZero_homology

/-- The connecting morphism `H^{n-1}(NL_{C/B}) ⟶ Hⁿ(C(g)[-1])` of the cone vanishes in every
degree `n ≠ 0`: for `n = 1` because `H⁰(g)` is an epimorphism and the composite with it is zero,
and otherwise because its source is a zero object. -/
theorem spaceNaiveCotangentConeHomologyConnecting_eq_zero (n : ℤ) (hzero : n ≠ 0) :
    spaceNaiveCotangentConeHomologyConnecting A B C a b (n - 1) n (by ring) = 0 := by
  by_cases h1 : n = 1
  · subst h1
    have hepi := epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero A B C a b
    refine (cancel_epi (HomologicalComplex.homologyMap
      (spaceRelativeNaiveCotangentComplexMap A B C a b) 0)).1 ?_
    rw [comp_zero]
    exact CochainComplex.homologyMap_comp_coneHomologyConnecting
      (spaceRelativeNaiveCotangentComplexMap A B C a b) 0 1 (by ring)
  · exact (HomologicalComplex.ExactAt.of_isZero
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b (n - 1)
        (by omega) (by omega))).isZero_homology.eq_of_src _ _

/-- **Stacks 0E1Y: the canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` is an isomorphism on
cohomology sheaves in every degree other than `-1`.**  In degree `0` this is
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`; in the remaining
degrees both sides vanish, the shifted cone because the connecting morphism into it is zero and
the projection out of it lands in a zero object. -/
theorem isIso_homologyMap_spaceNaiveCotangentConeMap_of_ne_negOne (n : ℤ) (hneg : n ≠ -1) :
    IsIso (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) n) := by
  by_cases hzero : n = 0
  · subst hzero
    infer_instance
  · have hmono : Mono (HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) n) :=
      (ShortComplex.exact_iff_mono _
        (spaceNaiveCotangentConeHomologyConnecting_eq_zero A B C a b n hzero)).1
        (spaceNaiveCotangentCone_homology_exact_cone A B C a b (n - 1) n (by ring))
    exact isIso_of_isZero_of_mono _ (HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) n)
      (isZero_homology_spaceBaseChangeNaiveCotangentComplex A B C a b n hneg hzero)
      (HomologicalComplex.ExactAt.of_isZero
        (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) n
          hneg hzero)).isZero_homology

/-- **Stacks 0E1Y: the canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` is a quasi-isomorphism as
soon as `H^{-1}(NL_{B/A} ⊗_B C)` vanishes.**

In degree `0` the map is an isomorphism unconditionally
(`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`) and in degrees other
than `-1` and `0` both cohomology sheaves vanish.  In degree `-1` the map is an epimorphism
unconditionally (`Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`), so
the hypothesis forces its target to vanish as well. -/
theorem quasiIso_spaceNaiveCotangentConeMap
    (h : IsZero ((spaceBaseChangeNaiveCotangentComplex A B C a b).homology (-1))) :
    QuasiIso (spaceNaiveCotangentConeMap A B C a b) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hneg : n = -1
    · subst hneg
      have := epi_homologyMap_spaceNaiveCotangentConeMap_negOne A B C a b
      exact isIso_of_isZero_of_epi _ h
    · exact isIso_homologyMap_spaceNaiveCotangentConeMap_of_ne_negOne A B C a b n hneg

end Space

/-! ### Ringed spaces -/

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 0E1Z: the canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` is a
quasi-isomorphism as soon as `H^{-1}(f^*NL_{Y/Z})` vanishes.** -/
theorem quasiIso_ringedSpaceNaiveCotangentConeMap
    (h : IsZero ((pulledNaiveCotangentComplex f g).homology (-1))) :
    QuasiIso (ringedSpaceNaiveCotangentConeMap f g) := by
  have h' : IsZero ((spaceBaseChangeNaiveCotangentComplex (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)).homology (-1)) :=
    IsZero.of_iso h
      (Stacks.NaiveCotangentSixTermSequence.homologyIsoOfComplexIso
        (pulledNaiveCotangentComparison f g) (-1)).symm
  have := quasiIso_spaceNaiveCotangentConeMap (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
    (ringedSpaceStructureMap f) h'
  rw [ringedSpaceNaiveCotangentConeMap]
  infer_instance

end RingedSpace

end Stacks.SheafOfModules

namespace Stacks.NaiveCotangentConeInvertible

open Stacks.SheafOfModules
open Stacks.NaiveCotangentSixTermSequence

/-! ### Schemes -/

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y)

/-- For `g` formally smooth the degree `-1` cohomology sheaf of `i^*NL_{P/Y}` vanishes, in the
inverse-image-then-extend-scalars model of the pullback.  This is the pullback step of
[Stacks Project, Tag 0FV4], proved at the termwise-pullback model, carried to the model the
canonical map of [Stacks Project, Tag 0E1Z] is stated at by
`Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso`. -/
theorem isZero_homology_negOne_pullbackNaiveCotangentComplex
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsZero ((pullbackNaiveCotangentComplex i g).homology (-1)) :=
  IsZero.of_iso
    (NaiveCotangentPullbackFormallySmooth.isZero_homology_negOne_modulePullbackNaiveCotangentComplex
      i g hg)
    (homologyIsoOfComplexIso (pullbackComplexIso i g) (-1))

/-- **The first missing step of [Stacks Project, Tag 0FV4]: the canonical map
`i^*NL_{P/Y} ⟶ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` of [Stacks Project, Tag 0E1Z] is a
quasi-isomorphism** for `g` formally smooth and `i` an arbitrary morphism of schemes. -/
theorem quasiIso_coneMap (hg : Stacks.Smooth.FormallySmoothScheme g) :
    QuasiIso (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom i) (ringedSpaceHom g)) :=
  quasiIso_ringedSpaceNaiveCotangentConeMap _ _
    (isZero_homology_negOne_pullbackNaiveCotangentComplex i g hg)

/-! ### The triangle in the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Pretriangulated

/-- The canonical map of [Stacks Project, Tag 0E1Z] is invertible in `D(𝒪_X)`. -/
theorem isIso_Q_map_coneMap (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsIso (DerivedCategory.Q.map
      (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom i) (ringedSpaceHom g))) :=
  have : QuasiIso (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom i) (ringedSpaceHom g)) :=
    quasiIso_coneMap i g hg
  inferInstance

/-- The canonical isomorphism `i^*NL_{P/Y} ≅ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` in `D(𝒪_X)`. -/
noncomputable def coneMapIso (hg : Stacks.Smooth.FormallySmoothScheme g) :=
  have := isIso_Q_map_coneMap i g hg
  asIso (DerivedCategory.Q.map
    (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom i) (ringedSpaceHom g)))

/-- The isomorphism is the canonical map of [Stacks Project, Tag 0E1Z]. -/
@[simp] theorem coneMapIso_hom (hg : Stacks.Smooth.FormallySmoothScheme g) :
    (coneMapIso i g hg).hom = DerivedCategory.Q.map
      (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom i) (ringedSpaceHom g)) :=
  rfl

/-- The triangle of [Stacks Project, Tag 0FV4]: the distinguished triangle of
[Stacks Project, Tag 0FV3] on the canonical map `NL_{X/Y} ⟶ NL_{X/P}`, with its first vertex
rewritten as `i^*NL_{P/Y}` by the canonical map of [Stacks Project, Tag 0E1Z]. -/
noncomputable def cotangentTriangle (hg : Stacks.Smooth.FormallySmoothScheme g) :=
  Triangle.mk
    ((coneMapIso i g hg).hom ≫
      (Stacks.NaiveCotangentCompositionTriangle.triangle
        (ringedSpaceHom i) (ringedSpaceHom g)).mor₁)
    (Stacks.NaiveCotangentCompositionTriangle.triangle
      (ringedSpaceHom i) (ringedSpaceHom g)).mor₂
    ((Stacks.NaiveCotangentCompositionTriangle.triangle
        (ringedSpaceHom i) (ringedSpaceHom g)).mor₃ ≫ ((coneMapIso i g hg).inv)⟦(1 : ℤ)⟧')

/-- **The triangle of [Stacks Project, Tag 0FV4] is distinguished.** -/
theorem cotangentTriangle_distinguished (hg : Stacks.Smooth.FormallySmoothScheme g) :
    cotangentTriangle i g hg ∈ distTriang _ :=
  distTriang_mk_of_iso_obj₁ _
    (Stacks.NaiveCotangentCompositionTriangle.triangle_distinguished
      (ringedSpaceHom i) (ringedSpaceHom g)) (coneMapIso i g hg)

/-- **The rotation of the triangle of [Stacks Project, Tag 0FV4]**, which exhibits `NL_{X/Y}` as
the cone of a map `NL_{X/P}[-1] ⟶ i^*NL_{P/Y}`. -/
theorem invRotate_cotangentTriangle_distinguished
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    (cotangentTriangle i g hg).invRotate ∈ distTriang _ :=
  inv_rot_of_distTriang _ (cotangentTriangle_distinguished i g hg)

/-! ### Reading the rotated triangle through the conormal sheaf and the differentials -/

/-- **`i^*NL_{P/Y} ≅ i^*Ω_{P/Y}[0]` in `D(𝒪_X)`**, in the inverse-image-then-extend-scalars
model of the pullback that the canonical map of [Stacks Project, Tag 0E1Z] is stated at: the
comparison `Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso` of the two models of the
pullback, followed by the pullback step of [Stacks Project, Tag 0FV4] read in the derived
category. -/
noncomputable def derivedPullbackDifferentialsIso
    (hg : Stacks.Smooth.FormallySmoothScheme g) :=
  DerivedCategory.Q.mapIso (pullbackComplexIso i g) ≪≫
    @asIso _ _ _ _ _
      (NaiveCotangentPullbackFormallySmooth.isIso_Q_map_pullbackNaiveCotangentToDifferentialsSingle
        i g hg)

/-- **`𝒞_{X/P}[1] ≅ NL_{X/P}` in `D(𝒪_X)`** for an immersion `i`: the quasi-isomorphism of
[Stacks Project, Tag 0FV2] read in the derived category. -/
noncomputable def derivedConormalShiftIso [IsImmersion i] :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (Stacks.Conormal.Sites.conormalShiftComparison i))
    (have : QuasiIso (Stacks.Conormal.Sites.conormalShiftComparison i) :=
      Stacks.Conormal.Sites.quasiIso_conormalShiftComparison i
    inferInstance)

/-- The rotated triangle of [Stacks Project, Tag 0FV4] with all three vertices rewritten:

`𝒞_{X/P}[1][-1] ⟶ i^*Ω_{P/Y}[0] ⟶ NL_{X/Y} ⟶ 𝒞_{X/P}[1]`.

The first vertex is `NL_{X/P}[-1]` read through [Stacks Project, Tag 0FV2], the second is
`i^*NL_{P/Y}` read through the pullback step, and the third is the naive cotangent complex of
`i ≫ g` itself, the iterated spelling of the composition triangle being removed by
`Stacks.NaiveCotangentSixTermSequence.totalCompIso`. -/
noncomputable def conormalDifferentialsTriangle [IsImmersion i]
    (hg : Stacks.Smooth.FormallySmoothScheme g) :=
  Triangle.mk
    (((CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso (derivedConormalShiftIso i)).hom ≫
        (cotangentTriangle i g hg).invRotate.mor₁ ≫
      (derivedPullbackDifferentialsIso i g hg).symm.inv)
    ((derivedPullbackDifferentialsIso i g hg).symm.hom ≫
        (cotangentTriangle i g hg).invRotate.mor₂ ≫
      (DerivedCategory.Q.mapIso (totalCompIso i g)).inv)
    ((DerivedCategory.Q.mapIso (totalCompIso i g)).hom ≫
      (cotangentTriangle i g hg).invRotate.mor₃ ≫
        (((CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso
          (derivedConormalShiftIso i)).inv)⟦(1 : ℤ)⟧')

/-- **`NL_{X/Y}` is the cone of a map from the conormal sheaf in degree `-1` to `i^*Ω_{P/Y}` in
degree `0`.**  For `i : X ⟶ P` an immersion of schemes and `g : P ⟶ Y` formally smooth the
triangle

`𝒞_{X/P}[1][-1] ⟶ i^*Ω_{P/Y}[0] ⟶ NL_{X/Y} ⟶ 𝒞_{X/P}[1]`

is distinguished in `D(𝒪_X)`.

This is the shape of the conclusion of [Stacks Project, Tag 0FV4]; what identifies the cone with
the two-term complex of the conormal sequence is the identification of the first morphism with
the conormal differential of [Stacks Project, Tag 01UZ], which is not available.  See the
`Scope` section of this file. -/
theorem conormalDifferentialsTriangle_distinguished [IsImmersion i]
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    conormalDifferentialsTriangle i g hg ∈ distTriang _ :=
  distTriang_mk_of_iso _ (invRotate_cotangentTriangle_distinguished i g hg)
    ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso (derivedConormalShiftIso i))
    (derivedPullbackDifferentialsIso i g hg).symm
    (DerivedCategory.Q.mapIso (totalCompIso i g))

end Derived

end Stacks.NaiveCotangentConeInvertible

end
