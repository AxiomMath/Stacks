module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Comparison

/-!
# Why Stacks Tag 01QK's square is not a consequence of Tag 01QJ

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ —
Stacks Tag 01QJ produces for each quasi-coherent `𝓕` a comparison `θ_𝓕 : f^* M̃ ⟶ 𝓕`, where
`M = Γ_*(X, 𝓛, 𝓕)`. Stacks Tag 01QK is a Remark whose entire content is that the square

```
      f^*M̃ ⊗_{𝒪_X} f^*𝒪_Y(n)  ────▶  f^*(M(n)~)
               │                            │
     θ_𝓕 ⊗ θ_{𝓛^{⊗n}}              θ_{𝓕 ⊗ 𝓛^{⊗n}}
               ▼                            ▼
         𝓕 ⊗ 𝓛^{⊗n}  ──── id ────▶   𝓕 ⊗ 𝓛^{⊗n}
```

commutes, the top arrow being the pullback of the multiplication map `M̃ ⊗ 𝒪_Y(n) → M(n)~` of
Constructions Equation 01MQ and the bottom arrow the identity. The source says "Proof omitted."
Since both bottom corners are one object and the bottom arrow is `id`, the whole assertion is the
single equation `θ_𝓕 ⊗ θ_{𝓛^{⊗n}} = f^*(mult) ≫ θ_{𝓕 ⊗ 𝓛^{⊗n}}`, modulo the identification
`M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗n})` the Remark calls obvious.

**This file does not prove that square, and it carries no `@[stacks 01QK]` attribute. It proves
instead that the square cannot be proved from the library's statement of Tag 01QJ**, and the proof
of that is the mathematical content here rather than a note in a docstring.

The binder form of Tag 01QJ's comparison is
`Stacks.SectionRingProjQuasicoherent.pullbackComparison L hL c :
pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules`, which takes Tag 0B5I's family `M̃ ⟶ f_*𝓕` as the
binder `c` and transposes it across `f^* ⊣ f_*`. Nothing constrains `c` beyond naturality in
`𝓕`. Now read the square as an equation in `θ`: its left-hand side `θ_𝓕 ⊗ θ_{𝓛^{⊗n}}` is
*quadratic* in `θ`, while its right-hand side `f^*(mult) ≫ θ_{𝓕 ⊗ 𝓛^{⊗n}}` is *linear* in `θ`,
the top arrow mentioning no `θ` at all. A quadratic form and a linear form that agree must agree
after negating `θ`, and negation fixes the one and reverses the other; so the common value is
`2`-torsion. Negation is the right perturbation to use rather than doubling, because `-θ` is a
natural isomorphism exactly when `θ` is, with inverse `-θ⁻¹`: the obstruction therefore survives
Tag 01QJ's full assertion that `θ` is a natural *iso*, not merely Tag 01QJ clause (b)'s
naturality, and it survives replacing `c` by `-c`.

So Tag 01QK is not a corollary of Tag 01QJ. It is the extra statement that `θ` is the comparison
built from a *multiplication-compatible* family on `Y`, and `pullbackComparison`'s binder `c`
cannot see multiplication: it mentions no twist, no multiplication map and no degree-`n` object.

## Main results

All in the namespace `Stacks.SectionRingProjQuasicoherent.TwistCompatibility`.

* `add_self_tensorHom_eq_zero`: the shape obstruction in a preadditive monoidal category. If a
  `⊗ₘ` of two morphisms equals a composite whose second factor is one morphism, and the same
  holds after negating all three, then the common value is `2`-torsion.
* `pullbackComparison_app_neg`: Tag 01QJ's comparison is odd in its binder —
  `pullbackComparison L hL (-c)` is `-pullbackComparison L hL c` componentwise. This is a fact
  about the Tag 01QJ declaration and is independent of Tag 01QK.
* `add_self_eq_zero_of_twistSquare`: **the obstruction, at an arbitrary natural comparison.** For
  any `θ : pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules`, any `𝓕`, `𝓖`, and any top arrow `t` not
  mentioning `θ`, if Tag 01QK's equation holds for `θ` and for `-θ` then the common value
  `θ.app 𝓕 ⊗ₘ θ.app 𝓖` is `2`-torsion.
* `add_self_eq_zero_of_twistSquare_of_comparison`: the same with `θ` spelled as
  `pullbackComparison L hL c`, the perturbation spelled as the binder `-c` that Tag 01QJ itself
  admits.
* `not_forall_twistSquare`: **the headline.** As soon as one instance of the square's left-hand
  side fails to be `2`-torsion, Tag 01QK's equation holds for no `θ`-free top arrow uniformly in
  Tag 0B5I's binder. So the Remark is not a consequence of the library's Tag 01QJ.

## Implementation notes

The top arrow is left as an arbitrary morphism `t` between the two corners rather than written
out as `f^*(moduleTwistMap) ≫ (identifications)`. That is not laziness: it makes the obstruction
*stronger* and it dodges three spelling problems at once.

* The obstruction holds for **every** `θ`-free top arrow, so no choice of the two identifications
  the Remark calls obvious, and no choice of route through the pullback–tensor comparison, can
  rescue the square. Writing one particular `t` out would prove less.
* `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` (Equation 01MQ) and
  `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` (the pullback–tensor comparison) are
  stated for `Stacks.SheafOfModules.Tensor.sheafTensor`, whereas `Γ_*(X, 𝓛, 𝓕)` and the `⊗` of
  this file's statements are the localized monoidal structure
  `Stacks.SheafInternalHom.schemeMonoidalCategory`. The two are related by
  `Stacks.SheafOfModules.tensorObjIso` with its coherence suite in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalInduced.lean`. Any composite through
  either is still a `t`.
* The identification of the top-right corner **does** exist, at the level at which it is
  true. It is `Stacks.SectionRingProjTheta.twistShiftSheafIso` of
  `StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistShift.lean`: an isomorphism
  `(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~ ≅ (Γ_*(X, 𝓛, 𝓕)(n))~` on `Proj Γ_*(X, 𝓛)`, with no hypotheses
  beyond the ambient category. What is *not* available is the corresponding statement about
  graded modules, and `moduleGrading_shift_neg_one` there makes that a theorem rather than a gap
  in the formalization — see input 3 below. Leaving the top arrow as `t` still proves more: the
  obstruction then covers every composite through that isomorphism as well as every other route.

`MonoidalPreadditive X.Modules` is not available and is assembled here from
`Stacks.SectionRingGeometric.tensorLeftAdditive` and `tensorRightAdditive`, transported to
Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling; only `schemeTensorRightAdditive` had been
transported before. `(Scheme.Modules.restrictFunctor f).Additive` is likewise missing from
Mathlib and is obtained from `Scheme.Modules.restrictFunctorIsoPullback` and the additivity of
`Scheme.Modules.pullback`, which Mathlib does provide.

`neg_tensorHom` and `tensorHom_neg` are derived from `MonoidalPreadditive.add_tensor` and
`tensor_add` rather than from `tensorHom_def` and `Functor.map_neg`, so that nothing in the
`Abstract` section depends on `tensorLeft`/`tensorRight` being recognised as functors — the
scheme-level instances arrive by a different route.

## What is not done here

**Tag 01QK's square is not proved here, and no `@[stacks 01QK]` attribute is attached in this
file.** Both assertions of the tag are proved, with no hypothesis, for the *constructed*
comparison `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison`, and carry the
attribute there:
`Stacks.SectionRingProjTheta.twistSquareInt` (assertion (ii), in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistRemarkSquareInt.lean`) and
`Stacks.SectionRingProjTheta.projTheta_app_eq_twistThetaInt` (assertion (i), in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistRemarkNormalization.lean`). The
obstruction of this file concerns the binder form `pullbackComparison` only. For that form,
`Stacks.SectionRingProjTheta.pullbackComparison_tensorHom` in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistSquare.lean` supplies the
characterisation of `c` that the obstruction below proves to be necessary — the
multiplication-compatibility of Tag 0B5I's family, on the `Proj` side — as a named hypothesis
and derives the square from it by the mate calculus.
`Stacks.SectionRingProjTheta.pullbackComparison_tensorHom_iff_mulComm`, in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistSquareIff.lean`, proves that
characterisation *equivalent* to the square it is used to derive, so that declaration's content
is the transport across the adjunction and not a property of Tag 0B5I's family. The results here
and there bracket the same statement from the two sides and are not in tension;
`Stacks.SectionRingProjTheta.add_self_eq_zero_of_mulComm_neg` shows that the perturbation used
here is inadmissible once the compatibility is imposed, which is exactly what an equivalent
hypothesis must do.

Neither is the Remark's first assertion, that Tag 01QI's isomorphism
`f^*𝒪_Y(n) → 𝓛^{⊗n}` "is just `θ_{𝓛^{⊗n}}`"; the negation argument of this file applies to it
verbatim, because its other side mentions no `θ` either, and that is carried out in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistNormalization.lean`. For the binder
form, three inputs were recorded as missing, in increasing cost; for the constructed comparison
they are supplied by `twistPowIdent` and `twistModuleIdent` of `TwistRemarkSquareInt.lean`, and
the first assertion is `projTheta_app_eq_twistThetaInt`.

1. **Tag 01QI's second claim is proved, and the maps `f^*𝒪_Y(n) → 𝓛^{⊗n}` it is about are in
  the library too.**
  The maps are `Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta (grading L)
  (canonicalSections L)`, Tag 01NK's `θ` at `ψ` the identity map of `Γ_*(X, 𝓛)` — Situation
  01QH equips `f` with them rather than Tag 01QI constructing them — and are also available under
  the name `Stacks.SectionRingProjMorphism.Theta.projTheta` as clause (2) of Tag 01PZ, with
  `Stacks.SectionRingProjMorphism.Theta.homOfLE_projHom_eq_glued` identifying the morphism it is
  taken along with `Stacks.SectionRingProjMorphism.projHom`. Their degree-`n` components are the
  Remark's left-hand side. `StacksFrontier/AlgebraicGeometry/SectionRingProjGoodOpen/Basic.lean`
  carries `@[stacks 01QI]` on `projHomOfIsAmple_preimage_whereInvertible` for the *first* claim
  (that `f` lands in the good open `W₁`), and
  `Stacks.SectionRingProjTwistIso.isIso_projTheta_app_of_forall_nvLocus` carries it for the
  second, in every degree `n ≥ 0` in which `𝓛^{⊗n}` is globally generated — hence, by
  `exists_isIso_projTheta_app`, in all large degrees for `𝓛` ample.
  Supplying the map by *defining* it as `θ_{𝓛^{⊗n}}` would turn the assertion into a tautology
  and is not done.
  **None of this makes the Remark's first assertion provable**, and none of it weakens the
  obstruction of this file by anything: that obstruction quantifies over every candidate
  morphism, and `not_forall_app_eq_of_iso` of the file named above over every candidate
  *isomorphism*, between the two corners, so it covers these maps as soon as they can be typed
  against `θ_{𝓛^{⊗n}}` — which is input 2 below, and is the only thing still in the way.
2. **`Γ_*(X, 𝓛, 𝓛^{⊗n}) ≅ S(n)` is missing**, so `θ_{𝓛^{⊗n}}` cannot be typed as a map out of
  `f^*𝒪_Y(n)`: its source is `f^*(Γ_*(X, 𝓛, 𝓛^{⊗n}))~`. It is what turns the square's lower-left
  tensor factor into the Remark's `f^*𝒪_Y(n)`. It is the case `𝓕 = 𝒪_X` of input 3, so the
  analysis recorded there applies to it: for `n ≥ 1` it is false as a statement about graded
  modules, for the repository's `ℕ`-truncated `Γ_*`, and true on the associated sheaves. At that
  level it is proved — `Stacks.SectionRingProjTheta.twistShiftSheafIso` read at `𝓕 = 𝒪_X`,
  with `twistPow_unit` pinning the left-hand corner — and what is left is the identification of
  `Stacks.TwistedSections.twistModule (𝟙_ C) L` with the section ring's integer grading.
3. **`Γ_*(X, 𝓛, 𝓕)(n) ≅ Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗n})` is missing *as a statement about graded
  modules*, and that is because it is false there; on the associated sheaves it is proved.**
  This is the identification the Remark calls obvious.
  `StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistShift.lean` settles both halves:
  `moduleGrading_shift_neg_one` proves the graded-module form false for this repository's `Γ_*`,
  and `isIso_twistShiftSheafMap` with `twistShiftSheafIso` proves the sheaf-level form, over
  `Proj Γ_*(X, 𝓛)`, with no hypotheses beyond the ambient category. Separately,
  `StacksFrontier/AlgebraicGeometry/TwistedSectionsShift/Basic.lean`
  proves it abstractly, as `Stacks.Monoidal.ModuleSystem.powShiftEquiv` with
  `powShiftEquiv_sectionSMul`, for `Stacks.Monoidal.ModuleSystem` and its own `shift`, without
  instantiating it at `Stacks.TwistedSections.twistModule`; the comparison with
  `Stacks.GradedModule.shiftedGrading` is what `twistShiftSheafMap` is stated against. What
  `moduleTwistMap` still
  needs is the tensor-structure bridge of the first bullet above, not this one.

  **It cannot be instantiated at `Stacks.TwistedSections.twistModule` as a statement about
  graded modules, and that is a defect of the spelling rather than of the Remark.** The
  repository's `Γ_*(X, 𝓛, 𝓕)` — the one `tildeFunctor` is built from, through
  `Stacks.SectionRingProjQuasicoherent.gradedTwistedSections` — is
  `Stacks.TwistedSections.twistModule F L = ⨁ m : ℕ, twistSections F L m`, graded by
  `Stacks.TwistedSections.moduleGrading`, which is `⊥` in every negative degree. The source's
  `Γ_*(X, 𝓛, 𝓕)` of Modules Definition 01CV is graded over all of `ℤ`. For `n ≥ 1` the shift
  `M(n)` therefore has `M(n)(-1) = M(n - 1) ≠ 0` while
  `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗n})(-1) = ⊥`, so the two are not isomorphic as graded modules. What
  survives is the comparison of their *associated sheaves*, and that is what
  `twistShiftSheafIso` is: the comparison is injective in every degree and surjective from
  degree `0` on, so the finitely many degrees where it fails are invisible to the associated
  sheaf. The identification the Remark needs is at that level, and it is proved.
  `powShiftEquiv`'s instantiation would deliver the graded-module statement instead, which is
  the one that is false here.

**None of the three would make the square provable**, which is this file's point: with `c`
unconstrained the square is false, so the decisive missing input is not an identification at all
but a *characterisation* of Tag 0B5I's family `c` — its compatibility with the multiplication of
Equation 01MQ. `StacksFrontier/AlgebraicGeometry/TwistedSectionsShift/Basic.lean` names Stacks
Lemma 28.18.2, the isomorphism `Γ_*(X, 𝓛, 𝓕)_{(s)} → Γ(X_s, 𝓕)`, as the cheapest input that
would construct `θ` outright instead of binding it; a `θ` so constructed is multiplication-
compatible by construction and Tag 01QK becomes unconditional. Both parts of Stacks Lemma
28.18.2 are proved, as `Stacks.SheafOfModules.sectionLocalizationMap_injective` and
`sectionLocalizationMap_bijective`; what stands between them and a constructed `θ` is the change
of graded ring recorded there, whose additive half is available as
`Stacks.SectionRingProjTheta.schemeSectionRingAddEquiv` with
`map_grading_eq_sectionRingGrading`, the multiplicative half not.

**Tag 0B5I itself is not the gap.** It is proved, in full and unconditionally, as
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparisonStatement`
`.comparison_existsUnique_functorial_degreeZeroId`: for a graded ring `𝒮` and a sheaf `ℱ` on
`Proj 𝒮` there is a unique comparison `M̃ ⟶ ℱ`, functorial in `ℱ`, which is the identity in
degree zero. What the binder `c` of this file needs is that family with `ℱ = f_*𝓕` *and* with
its source rewritten from `(Γ_*(Proj 𝒮, 𝒪(1), f_*𝓕))~` to `(Γ_*(X, 𝓛, 𝓕))~`, which is the
section ring comparison of Tag 01PW — the same identification assertion (i) of the Remark is
about. So the distance from Tag 0B5I to a constructed `c` is that comparison, not Tag 0B5I.

Nothing is claimed about `θ` beyond what is written: no iso-ness (Tag 01QJ's assertion that the
comparison is an isomorphism is `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison_spec`,
at the constructed family `Stacks.SectionRingProjQuasicoherent.tildeToPushforward`), no
comparison of the two tensor products on `X.Modules`, and no statement that any particular `t` is
or is not the pullback of Equation 01MQ's multiplication map.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Equation 27.10.0.4, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.SectionRingProjQuasicoherent.TwistCompatibility

/-! ### The shape obstruction

A quadratic expression and a linear expression in one morphism cannot agree uniformly: negating
the morphism fixes the first and reverses the second. This section is pure category theory and
mentions nothing about `Proj`.
-/

section Abstract

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- `⊗ₘ` is odd in its left argument. Derived from `MonoidalPreadditive.add_tensor` and
`zero_tensor`, so that no functoriality of `tensorRight` is needed. -/
theorem neg_tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : (-f) ⊗ₘ g = -(f ⊗ₘ g) := by
  have h : (-f) ⊗ₘ g + f ⊗ₘ g = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel, MonoidalPreadditive.zero_tensor]
  exact add_eq_zero_iff_eq_neg.mp h

/-- `⊗ₘ` is odd in its right argument. -/
theorem tensorHom_neg {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ₘ (-g) = -(f ⊗ₘ g) := by
  have h : f ⊗ₘ (-g) + f ⊗ₘ g = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel, MonoidalPreadditive.tensor_zero]
  exact add_eq_zero_iff_eq_neg.mp h

/-- `⊗ₘ` is even under negating both arguments: the two signs cancel. This is the asymmetry the
obstruction runs on, the composite `m ≫ w` being odd in `w`. -/
theorem neg_tensorHom_neg {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    (-f) ⊗ₘ (-g) = f ⊗ₘ g := by
  rw [neg_tensorHom, tensorHom_neg, neg_neg]

/-- **The shape obstruction.** Suppose `t ⊗ₘ t' = m ≫ w`, and suppose the same equation holds
after negating `t`, `t'` and `w` — which is what happens when all three are components of one
natural transformation and that transformation is negated, the morphism `m` mentioning none of
them. The left side is even under the negation and the right side is odd, so the common value is
`2`-torsion.

Stated additively rather than with `2 • _`, since that is the form the two sides come in. -/
theorem add_self_tensorHom_eq_zero {A B P Q R : C}
    (t : A ⟶ P) (t' : B ⟶ Q) (m : A ⊗ B ⟶ R) (w : R ⟶ P ⊗ Q)
    (h : t ⊗ₘ t' = m ≫ w) (hneg : (-t) ⊗ₘ (-t') = m ≫ (-w)) :
    (t ⊗ₘ t') + (t ⊗ₘ t') = 0 := by
  rw [neg_tensorHom_neg, Preadditive.comp_neg, ← h] at hneg
  exact add_eq_zero_iff_eq_neg.mpr hneg

end Abstract

/-! ### The obstruction at Tag 01QJ's comparison -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- Additivity of `tensorLeft` in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling. The
companion `Stacks.SectionRingGeometric.schemeTensorRightAdditive` had been transported but this
one had not, and `MonoidalPreadditive` needs both. -/
local instance schemeTensorLeftAdditive (X : Scheme.{u}) (L : X.Modules) :
    (tensorLeft L).Additive :=
  Stacks.SectionRingGeometric.tensorLeftAdditive X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- **`X.Modules` is monoidal preadditive.** Whiskering on either side is a functor whose
additivity is the transported `tensorLeftAdditive`/`tensorRightAdditive`.

`MonoidalCategory.tensorRight` is written out because `Stacks.tensorRight` — the sectionwise
tensor product of `PresheafOfModules (ringPresheaf O)` — is in the import closure, and the
enclosing namespace `Stacks` wins over the `open MonoidalCategory` of this file. There is no
`Stacks.tensorLeft`, so the left-hand fields need no prefix. -/
local instance schemeMonoidalPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules where
  whiskerLeft_zero := (tensorLeft _).map_zero _ _
  zero_whiskerRight := (MonoidalCategory.tensorRight _).map_zero _ _
  whiskerLeft_add _ _ := (tensorLeft _).map_add
  add_whiskerRight _ _ := (MonoidalCategory.tensorRight _).map_add

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsAmple X L)

/-- Restriction along an open immersion of schemes is additive. Mathlib proves
`(Scheme.Modules.pullback f).Additive` and `Scheme.Modules.restrictFunctorIsoPullback`, but does
not draw this conclusion. -/
local instance restrictFunctorAdditive [IsOpenImmersion (projHomOfIsAmple L hL)] :
    (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).Additive :=
  Functor.additive_of_iso
    (Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).symm

/-- The transposition of Tag 0B5I's family across the restriction adjunction is odd in that
family: `Scheme.Modules.restrictFunctor` is additive, so it carries `-c` to `-` its value. -/
theorem restrictComparison_app_neg [IsOpenImmersion (projHomOfIsAmple L hL)]
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) :
    (restrictComparison L hL (-c)).app F = -((restrictComparison L hL c).app F) := by
  change (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map ((-c).app F) ≫ _
    = -((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map (c.app F) ≫ _)
  rw [show (-c).app F = -(c.app F) from rfl, Functor.map_neg, Preadditive.neg_comp]

/-- **Tag 01QJ's comparison is odd in its binder.** Transposition across `f^* ⊣ f_*` is additive,
so negating Tag 0B5I's family `c` negates every component of `pullbackComparison L hL c`.

This is what makes the obstruction below bite on the library's declaration rather than on an
abstract `θ`: the perturbed comparison is again a `pullbackComparison`, for a binder `-c` that
Tag 01QJ admits on exactly the same terms as `c`. -/
theorem pullbackComparison_app_neg
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) :
    (pullbackComparison L hL (-c)).app F = -((pullbackComparison L hL c).app F) := by
  have : IsOpenImmersion (projHomOfIsAmple L hL) :=
    Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  obtain ⟨W, hW⟩ : ∃ W : (pullbackTildeFunctor L hL).obj F ⟶
      (tildeFunctor L ⋙ Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).obj F,
      ∀ d : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL),
        (pullbackComparison L hL d).app F = W ≫ (restrictComparison L hL d).app F :=
    ⟨_, fun _ => rfl⟩
  rw [hW, hW, restrictComparison_app_neg, Preadditive.comp_neg]

/-- **The obstruction, at an arbitrary natural comparison.** `t` stands for Tag 01QK's top arrow
— the pullback of Equation 01MQ's multiplication map, composed with whatever identifications
`M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` are used — and is arbitrary precisely because it mentions no
`θ`, which is the only thing the argument needs of it.

If Tag 01QK's equation holds for `θ` and for `-θ`, the common value is `2`-torsion. Both `θ` and
`-θ` are natural transformations `pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules`, and `-θ` is a natural
isomorphism whenever `θ` is, so no part of Tag 01QJ's assertion rules the perturbation out. -/
theorem add_self_eq_zero_of_twistSquare
    (θ : pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules) (F G : X.Modules)
    (t : (pullbackTildeFunctor L hL).obj F ⊗ (pullbackTildeFunctor L hL).obj G ⟶
      (pullbackTildeFunctor L hL).obj (F ⊗ G))
    (h : θ.app F ⊗ₘ θ.app G = t ≫ θ.app (F ⊗ G))
    (hneg : (-θ).app F ⊗ₘ (-θ).app G = t ≫ (-θ).app (F ⊗ G)) :
    (θ.app F ⊗ₘ θ.app G) + (θ.app F ⊗ₘ θ.app G) = 0 :=
  add_self_tensorHom_eq_zero (θ.app F) (θ.app G) t (θ.app (F ⊗ G)) h hneg

/-- **The obstruction, at the Tag 01QJ declaration.** The hypotheses are Tag 01QK's
equation for Tag 0B5I's family `c` and for `-c`; the conclusion is that the square's common
value is `2`-torsion.

Since `pullbackComparison`'s binder `c` is constrained by nothing — it mentions no twist, no
multiplication map and no degree-`n` object — `-c` is admissible whenever `c` is, and a proof of
Tag 01QK uniform in `c` would supply both hypotheses. Therefore **no such proof exists** unless
every instance of the square is `2`-torsion, which for a comparison that Tag 01QJ asserts to be
an isomorphism forces `2` to annihilate the relevant `Hom` group. This is the evidenced
obstruction: Tag 01QK needs a characterisation of `c`, not merely its existence. -/
theorem add_self_eq_zero_of_twistSquare_of_comparison
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (t : (pullbackTildeFunctor L hL).obj F ⊗ (pullbackTildeFunctor L hL).obj G ⟶
      (pullbackTildeFunctor L hL).obj (F ⊗ G))
    (h : (pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G =
      t ≫ (pullbackComparison L hL c).app (F ⊗ G))
    (hneg : (pullbackComparison L hL (-c)).app F ⊗ₘ (pullbackComparison L hL (-c)).app G =
      t ≫ (pullbackComparison L hL (-c)).app (F ⊗ G)) :
    ((pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G) +
        ((pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G) = 0 := by
  refine add_self_eq_zero_of_twistSquare L hL (pullbackComparison L hL c) F G t h ?_
  simp only [NatTrans.app_neg, ← pullbackComparison_app_neg]
  exact hneg

/-- **Tag 01QK's square, read as a statement uniform in Tag 0B5I's binder, is false.** The
hypothesis `hne` says that one instance of the square's left-hand side is not `2`-torsion — which
is what Tag 01QJ's assertion that `θ` is an isomorphism makes one expect, and what holds as soon
as the relevant `Hom` group has no `2`-torsion. Under it, no `θ`-free top arrow `t` makes the
equation hold for every admissible binder `d`.

This is the obstruction in its sharpest form, and it is why this file carries no
`@[stacks 01QK]`: the Remark is not a consequence of the library's Tag 01QJ. Making it provable
needs `c` *characterised* — its compatibility with Equation 01MQ's multiplication — not merely
bound; and assuming that characterisation adds nothing to the square, since
`Stacks.SectionRingProjTheta.pullbackComparison_tensorHom_iff_mulComm` proves it equivalent to
the square. The characterisation has to be *proved* of a constructed `c`; for the constructed
comparison `pullbackTildeComparison` that is done, and the square is
`Stacks.SectionRingProjTheta.twistSquareInt`, which carries `@[stacks 01QK]`. -/
theorem not_forall_twistSquare
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (t : (pullbackTildeFunctor L hL).obj F ⊗ (pullbackTildeFunctor L hL).obj G ⟶
      (pullbackTildeFunctor L hL).obj (F ⊗ G))
    (hne : ((pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G) +
      ((pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G) ≠ 0) :
    ¬ ∀ d : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL),
        (pullbackComparison L hL d).app F ⊗ₘ (pullbackComparison L hL d).app G =
          t ≫ (pullbackComparison L hL d).app (F ⊗ G) := fun h =>
  hne (add_self_eq_zero_of_twistSquare_of_comparison L hL c F G t (h c) (h (-c)))

end Scheme

end Stacks.SectionRingProjQuasicoherent.TwistCompatibility

end
