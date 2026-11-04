module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallySeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The second relative diagonal is the neutral section of the relative inertia

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. Write

`Δ_{f, 1} = Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

for the relative diagonal of `f` and `Δ_{f, 2} = Δ_{Δ_f}` for the diagonal of `Δ_f`, the *second
relative diagonal*. The proof of Stacks 0CL0 asserts that `Δ_{f, 2}` *is* the neutral section

`e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, 𝟙 x)`

of the relative inertia, and uses that identification to pass between its conditions (b) and (c)
"by definition". This file supplies it: the target of `Δ_{f, 2}` is the relative inertia, by an
equivalence **over the site**, and `Δ_{f, 2}` corresponds to `e` under that equivalence. It is the
relative counterpart of `AlgebraicGeometry.Stack.SecondDiagonalInertia`, which does the absolute
case for Stacks 07WG.

The consequence the conditions (c) of Stacks 0CL0 are stated in is drawn here too: the relative
property of Stacks 04XB is the same for `Δ_{f, 2}` and for `e`, for an *arbitrary* property of
morphisms of algebraic spaces over `S` and with no hypothesis on it, so in particular `Δ_{f, 2}`
is a closed immersion, quasi-compact, or an immersion exactly when `e` is.

## Main definitions

* `AlgebraicGeometry.Stack.secondRelativeDiagonalTarget`,
  `AlgebraicGeometry.Stack.secondRelativeDiagonal`: the target of the second relative diagonal,
  and the second relative diagonal itself.
* `AlgebraicGeometry.Stack.relativeInertiaNeutralSection`: the neutral section `e` of the
  relative inertia, as a 1-morphism of the 2-category of categories fibred in groupoids over the
  site, and `AlgebraicGeometry.Stack.relativeInertiaStackNeutralSection` the same 1-morphism read
  in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.secondRelativeDiagonalToRelativeInertia` and
  `AlgebraicGeometry.Stack.relativeInertiaToSecondRelativeDiagonal`: the comparison 1-morphism
  identifying the target of the second relative diagonal with the relative inertia, and its
  quasi-inverse.

## Main results

* `AlgebraicGeometry.Stack.secondRelativeDiagonal_comp_toRelativeInertia`: **the second relative
  diagonal is the neutral section of the relative inertia**, and
  `AlgebraicGeometry.Stack.relativeInertiaNeutralSection_comp_toSecondRelativeDiagonal` the same
  identification read through the quasi-inverse.
* `AlgebraicGeometry.Stack.relativeProperty_secondRelativeDiagonal_iff_neutralSection`: the
  relative property of Stacks 04XB holds for the second relative diagonal exactly when it holds
  for the neutral section, for an arbitrary property of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.isClosedImmersion_secondRelativeDiagonal_iff_neutralSection`,
  `AlgebraicGeometry.Stack.isQuasiCompact_secondRelativeDiagonal_iff_neutralSection`,
  `AlgebraicGeometry.Stack.isImmersion_secondRelativeDiagonal_iff_neutralSection`: the three
  instances of that equivalence which the conditions (c) of Stacks 0CL0 are stated in. The
  representability conjunct of Stacks 04YL transports too, by the result named
  `isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection` in this
  namespace.
* `AlgebraicGeometry.Stack.isLocallySeparated_relativeDiagonal_iff_isImmersion_neutralSection`:
  **conditions (b) and (c) of part (3) of Stacks 0CL0 are equivalent** — the relative diagonal of
  a 1-morphism of algebraic stacks is locally separated exactly when the neutral section of its
  relative inertia is an immersion of algebraic stacks. This is the identification above composed
  with Stacks 04YU read at `Δ_f`.

## Implementation notes

All the mathematics is the categorical statement of
`StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal`, which is proved there for an
arbitrary 1-morphism `G` of categories over an arbitrary base: the comparison functor
`CategoryTheory.TwoFibreProductOver.toRelativeInertia` sends `(x, y, φ)` to `(x, φ₁ ∘ φ₂⁻¹)`, the
identification of the second diagonal with the neutral section is
`CategoryTheory.TwoFibreProductOver.diagonal_comp_toRelativeInertia`, and the comparison is an
equivalence over the base by
`CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia`. Nothing here beyond the
hypothesis that `f` is a 1-morphism over the site — its `w` field — is used, and no stack, no
algebraicity and no representability hypothesis enters.

The target of the second relative diagonal is the iterated
`AlgebraicGeometry.Stack.twoFibreProduct`, so it is literally the
`CategoryTheory.TwoFibreProductOver.DiagonalFibreProduct` of `f.hom.w`, and the relative inertia
is the canonical `AlgebraicGeometry.Stack.relativeInertia`, whose underlying category over the
site is `CategoryTheory.RelativeInertia.basedCategory`. Both the comparison and its quasi-inverse
are therefore the categorical functors unchanged, with their compatibilities with the structure
functors as the `w` field, and no transport intervenes anywhere.

The universes are those of the 2-category of algebraic stacks — morphism universe `u`, object
universe `u + 1` — rather than free ones as in the absolute case. They are pinned because the
relative inertia is read as an object of the 2-category through
`AlgebraicGeometry.Stack.isFiberedInGroupoids_relativeInertia`, which is stated there; stating the
fibredness of the relative inertia again at free universes would be a second proof of an existing
statement. `AlgebraicGeometry.Stack.relativeDiagonal` must be written `.{u, u, u + 1}` at every
occurrence; without the pin its three universe arguments are not determined by the explicit
arguments and the file reports `stuck at solving universe constraint`.

The transport of the relative property is
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` (Stacks 0457 for the relative property
of Stacks 03YK) applied twice, once with the comparison as the horizontal 1-morphism of targets
and once with its quasi-inverse; it needs **no** hypothesis on the property, in particular neither
stability under base change nor locality at the target, so the three corollaries are
unconditional. The property is written out as the quantifier of Stacks 04XB rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in
`AlgebraicGeometry.Stack.SeparatedQuasiSeparatedAlgebraicStack`: that abbreviation carries two
instance arguments which it does not use and which this library does not have for every property
in question.

The step from the identification to conditions (b) and (c) of part (3) of Stacks 0CL0 is
Stacks 04YU read at `Δ_f` rather than at `f`, which
`AlgebraicGeometry.Stack.LocallySeparatedDiagonal` supplies; the representability hypothesis it
carries there is automatic by part (1) of Stacks 04XS. Its own route needs Stacks 04YR *over the
site* in the point-first orientation, and in particular not the absolute 2-fibre-product form of
Stacks 04YR, for `CategoryTheory.Limits.CategoricalPullback`, which does not serve — the
comparison isomorphism of an object of an absolute 2-fibre product is arbitrary and of a
relative one vertical, so the two notions are inequivalent, as
`AlgebraicGeometry.Stack.ImmersionMorphism` already records. Nothing of that form is used here
either: the identification is a statement about one cospan and the comparison is the categorical
one, so no base-change square of any kind is formed.

Only `AlgebraicGeometry.Stack.isLocallySeparated_relativeDiagonal_iff_isImmersion_neutralSection`
carries a `@[stacks]` attribute. The identification itself is a step of the proof of Stacks 0CL0
rather than one of its assertions; the key `0CL0 "local_separatedness"` has a covering set of two
theorems, part (3) (b) ⇔ (c) here and part (3) (a) ⇔ (b) in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia`.

The source proves (a) ⇔ (b) through (a) ⇔ (c), by choosing a surjective smooth 1-morphism from
an algebraic space `U`, forming `G = U ×_𝒳 I_{𝒳/𝒴}` as a *group* algebraic space over `U`
(Stacks 050Q, with the group law of Remark 050R) and citing Groupoids in Spaces,
Lemma 06P6, with Stacks 0CPK and Groupoids in Spaces, Lemma 0DSK for parts (4) and (5). Stacks
06P6 and 0DSK are Chapter 78 and both *are* in this library — 06P6 as
`AlgebraicGeometry.Space.isLocallySeparated_iff_identity_isImmersion` and its two siblings in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/Separation.lean`, 0DSK as
`AlgebraicGeometry.Space.isUnramified_of_isPseudoTorsor` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isPseudoTorsor` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/PseudoTorsorProperties.lean`.

What blocks each of the two is different, and they should not be lumped together. For 06P6 it is
the group-object structure on `I_{𝒳/𝒴}` it would be applied to: the composition law
`CategoryTheory.RelativeInertia.composition` (Stacks 050R) is there, its group-object axioms are
not. For 0DSK it is **not** that: the source applies 0DSK to a pseudo-torsor of
relative Isom sheaves, but on the route that file takes no Isom sheaf enters at all, because the
relative inertia projection is the base change of `Δ_f` along `Δ_f` and 0DSK's own argument is
available in the self-base-change form
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd`. See
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordRelativeInertia` for what is still owed.

Neither route is the one taken here, and none of parts (1), (2), (3) needs a group law at all:
the inertia projection is a base change of `Δ_f` in one direction and `Δ_{f, 2}` is a section of
that base change in the other. Parts (1) and (2) are
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationRelativeInertia`, by that same route.

## References

* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FibredInGroupoids

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The target `𝒳 ×_{Δ_f, 𝒳 ×_{f, 𝒴, f} 𝒳, Δ_f} 𝒳` of the second relative diagonal of a
1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`: the
2-fibre product of the relative diagonal of `f` with itself. -/
abbrev secondRelativeDiagonalTarget (f : 𝒳 ⟶ 𝒴) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS
    (twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS 𝒴 𝒳 𝒳 f.hom f.hom) 𝒳 𝒳
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f).hom
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f).hom

/-- The second relative diagonal `Δ_{f, 2} = Δ_{Δ_f}` of a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories
fibred in groupoids over the big fppf site of `S`: the relative diagonal of the relative diagonal
of `f`. -/
abbrev secondRelativeDiagonal (f : 𝒳 ⟶ 𝒴) : 𝒳 ⟶ secondRelativeDiagonalTarget B S hS f :=
  relativeDiagonal.{u, u, u + 1} B S hS 𝒳
    (twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS 𝒴 𝒳 𝒳 f.hom f.hom)
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)

/-- The neutral section `e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, 𝟙 x)`, of the relative inertia of a
1-morphism of categories fibred in groupoids over the big fppf site of `S`. It is strictly over
the site: the structure functor of the relative inertia is the forgetful functor followed by that
of `𝒳`. -/
abbrev relativeInertiaNeutralSection (f : 𝒳 ⟶ 𝒴) : 𝒳 ⟶ relativeInertia B S hS f :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.neutralSection f.hom.toFunctor
      w := rfl }

/-- The comparison 1-morphism from the target of the second relative diagonal to the relative
inertia, `(x, y, φ) ↦ (x, φ₁ ∘ φ₂⁻¹)`. It is a 1-morphism over the site by
`CategoryTheory.TwoFibreProductOver.toRelativeInertia_comp_relativeInertiaStruct`. -/
def secondRelativeDiagonalToRelativeInertia (f : 𝒳 ⟶ 𝒴) :
    secondRelativeDiagonalTarget B S hS f ⟶ relativeInertia B S hS f :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.toRelativeInertia f.hom.w
      w := TwoFibreProductOver.toRelativeInertia_comp_relativeInertiaStruct f.hom.w }

/-- The quasi-inverse of `AlgebraicGeometry.Stack.secondRelativeDiagonalToRelativeInertia`, which
sends an object `(x, α)` of the relative inertia to the object `(x, x, (α, 𝟙 x))` of the target of
the second relative diagonal. -/
def relativeInertiaToSecondRelativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    relativeInertia B S hS f ⟶ secondRelativeDiagonalTarget B S hS f :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.ofRelativeInertia f.hom.w
      w := TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor f.hom.w }

/-- The comparison 1-morphism is an equivalence of the underlying categories. -/
theorem isEquivalence_secondRelativeDiagonalToRelativeInertia (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence
      (secondRelativeDiagonalToRelativeInertia B S hS f).hom.toFunctor :=
  TwoFibreProductOver.isEquivalence_toRelativeInertia f.hom.w

/-- Its quasi-inverse is an equivalence of the underlying categories too. -/
theorem isEquivalence_relativeInertiaToSecondRelativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence
      (relativeInertiaToSecondRelativeDiagonal B S hS f).hom.toFunctor :=
  (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia f.hom.w)
    (TwoFibreProductOver.toRelativeInertia f.hom.w)
    (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia f.hom.w).symm)
    (TwoFibreProductOver.unitIso f.hom.w).symm).isEquivalence_functor

/-- **The second relative diagonal is the neutral section of the relative inertia.** Composing
`Δ_{f, 2} = Δ_{Δ_f}` with the comparison 1-morphism identifying the target of the second relative
diagonal with the relative inertia `I_{𝒳/𝒴}` gives the neutral section `x ↦ (x, 𝟙 x)`. This is
the identification the proof of Stacks 0CL0 uses to pass between its conditions (b) and (c). -/
theorem secondRelativeDiagonal_comp_toRelativeInertia (f : 𝒳 ⟶ 𝒴) :
    secondRelativeDiagonal B S hS f ≫ secondRelativeDiagonalToRelativeInertia B S hS f =
      relativeInertiaNeutralSection B S hS f :=
  Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext'
      (TwoFibreProductOver.diagonal_comp_toRelativeInertia f.hom.w))

/-- The same identification read through the quasi-inverse: composing the neutral section of the
relative inertia with it gives the second relative diagonal. -/
theorem relativeInertiaNeutralSection_comp_toSecondRelativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaNeutralSection B S hS f ≫
        relativeInertiaToSecondRelativeDiagonal B S hS f =
      secondRelativeDiagonal B S hS f :=
  Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' rfl)

/-- The 2-commutativity datum that `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` and
Stacks 0457 are fed in order to move a property from the neutral section to the second relative
diagonal: the composite of `Δ_{f, 2}` with the comparison is the neutral section. -/
private def neutralSectionCompIso (f : 𝒳 ⟶ 𝒴) :
    BasedFunctor.comp (BasedFunctor.id 𝒳.val) (relativeInertiaNeutralSection B S hS f).hom ≅
      BasedFunctor.comp (secondRelativeDiagonal B S hS f).hom
        (secondRelativeDiagonalToRelativeInertia B S hS f).hom :=
  eqToIso (BasedCategory.BasedFunctor.ext'
    (TwoFibreProductOver.diagonal_comp_toRelativeInertia f.hom.w).symm)

/-- The 2-commutativity datum for the other direction: the composite of the neutral section with
the quasi-inverse of the comparison is `Δ_{f, 2}`. -/
private def secondRelativeDiagonalCompIso (f : 𝒳 ⟶ 𝒴) :
    BasedFunctor.comp (BasedFunctor.id 𝒳.val) (secondRelativeDiagonal B S hS f).hom ≅
      BasedFunctor.comp (relativeInertiaNeutralSection B S hS f).hom
        (relativeInertiaToSecondRelativeDiagonal B S hS f).hom :=
  eqToIso (BasedCategory.BasedFunctor.ext' rfl)

/-- The identity of `𝒳` is an equivalence, in the form the transport results take it. -/
theorem isEquivalence_basedFunctorId
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id 𝒵.val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.val.obj))

/-- **Representability by algebraic spaces of the second relative diagonal is representability of
the neutral section of the relative inertia.** This is Stacks 0457 along the comparison
1-morphism, which identifies the two 1-morphisms. -/
theorem isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection
    (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS (secondRelativeDiagonal B S hS f).hom ↔
      IsRepresentableByAlgebraicSpaces B S hS (relativeInertiaNeutralSection B S hS f).hom := by
  have ha := isEquivalence_basedFunctorId B S hS 𝒳
  have hb := isEquivalence_secondRelativeDiagonalToRelativeInertia B S hS f
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (secondRelativeDiagonal B S hS f).hom (relativeInertiaNeutralSection B S hS f).hom
    (BasedFunctor.id 𝒳.val) (secondRelativeDiagonalToRelativeInertia B S hS f).hom
    (neutralSectionCompIso B S hS f)).symm

/-- **The relative property of Stacks 04XB is the same for the second relative diagonal and for
the neutral section of the relative inertia**, for an arbitrary property `P` of morphisms of
algebraic spaces over `S` and with no hypothesis on `P`.

Both directions are `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, Stacks 0457 for
the relative property of Stacks 03YK, applied along the comparison 1-morphism in one direction and
along its quasi-inverse in the other; the 2-commutativity datum is in each case the identification
of the second relative diagonal with the neutral section. -/
theorem relativeProperty_secondRelativeDiagonal_iff_neutralSection
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (f : 𝒳 ⟶ 𝒴) :
    (∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ (secondRelativeDiagonalTarget B S hS f).val.obj)
        (_hy : y ⋙ (secondRelativeDiagonalTarget B S hS f).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p
            (secondRelativeDiagonalTarget B S hS f).val.p y
            (secondRelativeDiagonal B S hS f).hom.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) ↔
      (∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ (relativeInertia B S hS f).val.obj)
        (_hy : y ⋙ (relativeInertia B S hS f).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p (relativeInertia B S hS f).val.p y
            (relativeInertiaNeutralSection B S hS f).hom.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) := by
  have ha := isEquivalence_basedFunctorId B S hS 𝒳
  have hΘ := isEquivalence_secondRelativeDiagonalToRelativeInertia B S hS f
  have hΘinv := isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact relativeProperty_of_equivalences B S hS P
      (relativeInertiaNeutralSection B S hS f).hom (secondRelativeDiagonal B S hS f).hom
      (BasedFunctor.id 𝒳.val) (relativeInertiaToSecondRelativeDiagonal B S hS f).hom
      (secondRelativeDiagonalCompIso B S hS f) h
  · exact relativeProperty_of_equivalences B S hS P
      (secondRelativeDiagonal B S hS f).hom (relativeInertiaNeutralSection B S hS f).hom
      (BasedFunctor.id 𝒳.val) (secondRelativeDiagonalToRelativeInertia B S hS f).hom
      (neutralSectionCompIso B S hS f) h

/-- **Condition (1)(c) of Stacks 0CL0 is a condition on the second relative diagonal.** The second
relative diagonal of `f` is a closed immersion in the sense of Stacks 04XB exactly when the
neutral section of the relative inertia is. -/
theorem isClosedImmersion_secondRelativeDiagonal_iff_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsClosedImmersion B S hS (secondRelativeDiagonal B S hS f) ↔
      IsClosedImmersion B S hS (relativeInertiaNeutralSection B S hS f) :=
  relativeProperty_secondRelativeDiagonal_iff_neutralSection B S hS
    (Space.closedImmersionProperty B S hS) f

/-- **Condition (2)(c) of Stacks 0CL0 is a condition on the second relative diagonal.** The second
relative diagonal of `f` is quasi-compact in the sense of Stacks 04XB exactly when the neutral
section of the relative inertia is. -/
theorem isQuasiCompact_secondRelativeDiagonal_iff_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsQuasiCompact B S hS (secondRelativeDiagonal B S hS f) ↔
      IsQuasiCompact B S hS (relativeInertiaNeutralSection B S hS f) :=
  relativeProperty_secondRelativeDiagonal_iff_neutralSection B S hS
    (Space.quasiCompactProperty B S hS) f

/-- **Condition (3)(c) of Stacks 0CL0 is a condition on the second relative diagonal.** The second
relative diagonal of `f` is an immersion in the sense of Stacks 04XB exactly when the neutral
section of the relative inertia is. -/
theorem isImmersion_secondRelativeDiagonal_iff_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsImmersion B S hS (secondRelativeDiagonal B S hS f) ↔
      IsImmersion B S hS (relativeInertiaNeutralSection B S hS f) :=
  relativeProperty_secondRelativeDiagonal_iff_neutralSection B S hS
    (Space.immersionProperty B S hS) f

end FibredInGroupoids

section AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The neutral section `e : 𝒳 ⟶ I_{𝒳/𝒴}` of the relative inertia of a 1-morphism of algebraic
stacks over `S`, read in the 2-category of algebraic stacks: it is the 1-morphism of categories
fibred in groupoids `AlgebraicGeometry.Stack.relativeInertiaNeutralSection` unchanged, since the
1-morphisms of the 2-category of algebraic stacks are those of the ambient one. This is the
`Δ_{f, 2} = e` of Stacks 0CL0. -/
def relativeInertiaStackNeutralSection (f : 𝒳 ⟶ 𝒴) : 𝒳 ⟶ relativeInertiaStack B S hS f :=
  Bicategory.InducedBicategory.mkHom (relativeInertiaNeutralSection B S hS f.hom)

/-- The 1-morphism of categories fibred in groupoids underlying the neutral section of the
relative inertia of a 1-morphism of algebraic stacks is the neutral section of the relative
inertia of the underlying 1-morphism. -/
theorem relativeInertiaStackNeutralSection_hom (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaStackNeutralSection B S hS f).hom =
      relativeInertiaNeutralSection B S hS f.hom :=
  rfl

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the relative diagonal
`Δ_{f, 1} = Δ_f` is locally separated in the sense of Stacks 04XB exactly when
`Δ_{f, 2} = e : 𝒳 ⟶ I_{𝒳/𝒴}`, the neutral section of the relative inertia, is an immersion of
algebraic stacks in the sense of part (3) of Stacks 04YL.

This is Stacks 04YU read at `Δ_f` instead of at `f` — whose representability hypothesis is
automatic there by part (1) of Stacks 04XS — composed with the identification of `Δ_{f, 2}` with
the neutral section, which is what the source means by "since `Δ_{f, 2}` is the diagonal of
`Δ_f` we have (b) ⇔ (c) by definition". The transports of the two conjuncts of part (3) of
Stacks 04YL are `isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection`
and `isImmersion_secondRelativeDiagonal_iff_neutralSection`. -/
@[stacks 0CL0 "part (3), conditions (b) and (c): the relative diagonal is locally separated \
exactly when the neutral section of the relative inertia is an immersion"]
theorem isLocallySeparated_relativeDiagonal_iff_isImmersion_neutralSection (f : 𝒳 ⟶ 𝒴) :
    IsLocallySeparated B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) ↔
      AlgebraicStacks.IsImmersion B S hS (relativeInertiaStackNeutralSection B S hS f) :=
  (isLocallySeparated_iff_isImmersion_relativeDiagonalAlgebraicStacks B S hS
      (relativeDiagonalAlgebraicStacks B S hS f)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).trans
    (and_congr
      (isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection B S hS f.hom)
      (isImmersion_secondRelativeDiagonal_iff_neutralSection B S hS f.hom))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
