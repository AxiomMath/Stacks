module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension
import StacksCore.Tactic.StacksAttribute

/-!
# The assertions for torsion sheaves on curves are insensitive to a dense open

Let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
whose underlying space has dimension at most one, let `F` be a constructible torsion abelian
sheaf on the small étale site of `X` and let `j : X' ⟶ X` be the inclusion of a dense open
subscheme. Stacks Project Tag 0GJA asserts that the eight statements of Situation 0A52 hold for
`F` if and only if they hold for `j_! j^{-1} F`. The eight statements are the vanishing of
`H^q(X, F)` above degree two, its vanishing above degree one when `X` is affine and when `F` is
torsion of characteristic-primary exponent, the finiteness of `H^q(X, F)` for constructible `F`
of torsion prime to the characteristic and for constructible `F` on a proper `X`, the bijectivity
of the restriction map `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` along an extension `k'/k` of
algebraically closed fields in those same two cases, and the surjectivity of
`H²(X, F) → H²(U, F|_U)` for an open `U ⊆ X`.

The source proves all sixteen implications from one short exact sequence. If `i : Z ⟶ X` is the
closed immersion onto the complement of `X'`, then Tag 095L gives

```
0 ⟶ j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F ⟶ 0
```

and every one of the eight statements is an assertion about the cohomology of one of the three
terms, so the long exact sequence moves it between the sub-object `j_! j^{-1} F` and the ambient
`F` as soon as the cohomology of the closed part `i_* i^{-1} F` is known. That knowledge is what
density, the dimension bound and constructibility buy in the source, and it is carried here as
the hypothesis `Stacks.EtaleCohomology.ClosedComplementCohomology`.

## Main definitions

* `Stacks.EtaleCohomology.ClosedComplementCohomology` is the cohomological input the closed
  complement of a dense open supplies: its cohomology vanishes in positive degrees, is finite in
  degree zero, and restriction along the morphism of statements (6), (7) and (8) is bijective on
  it in every degree.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_extensionByZero_iff`: the eight statements of
  Situation 0A52 hold for `F` if and only if they hold for `j_! j^{-1} F`, given the cohomology of
  the closed complement and the transfer of the two torsion conditions. This is NOT Tag 0GJA and
  carries no tag attribute: see the note on the declaration for why two of those hypotheses are
  false as stated and what has to change before the tag can be registered.
* `Stacks.EtaleCohomology.curveCohomologyStatements_X₂_iff_X₁_of_shortExact` is the sixteen
  implications behind it, for an arbitrary short exact sequence whose quotient sheaf has the
  cohomology that the closed complement of a dense open has.
* `Stacks.EtaleCohomology.mapExt_bijective_of_shortExact_X₁` and
  `Stacks.EtaleCohomology.isBijectiveOnExt_of_shortExact_X₁`: an exact functor bijective on `Ext`
  into the ambient object and into the quotient of a short exact sequence, in every degree, is
  bijective on `Ext` into the sub-object in every degree.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁` and
  `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact`: the same
  transfer for the restriction map on étale cohomology, bijectivity in every degree and
  surjectivity in a single degree.
* `Stacks.EtaleCohomology.subsingleton_ext_X₁_of_shortExact` and
  `Stacks.EtaleCohomology.finite_ext_X₁_of_shortExact`: vanishing and finiteness of `Ext` pass
  from the ambient object and the quotient to the sub-object.

## Implementation notes

**Which direction of each transfer is new.** The six transfers towards the *middle* term of a
short exact sequence already exist — `Stacks.EtaleCohomology.subsingleton_ext_X₂_of_shortExact`
and `Stacks.EtaleCohomology.finite_ext_X₂_of_shortExact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/PrimaryVanishing.lean`,
`Stacks.EtaleCohomology.mapExt_bijective_of_shortExact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/CurveDevissage.lean`,
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_shortExact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/AlgClosedCase.lean` and
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/RestrictionLongExactSequence.lean`
— and they are what the implication "the statements for `j_! j^{-1} F` give the statements for
`F`" is built from. The opposite implication needs the same transfers towards the *sub-object*,
which did not exist, and the first half of this file supplies them. Each is a window of the same
covariant long exact sequence shifted by one place, so each has a degree-zero edge case where the
window runs off the left-hand end of `Ext`; there the transfer comes instead from the
monomorphism `S.f`, through `CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono`.

**What is carried as a hypothesis and why.** Three things, and none of them is a conclusion of the
theorem.

* `ClosedComplementCohomology`. Its three fields say that `H^q(X, i_* i^{-1} F)` vanishes for
  `q > 0`, is finite for `q = 0`, and has bijective restriction in every degree. This is where
  the entire geometric content of Tag 0GJA sits, and this library does not deliver it. In the
  source it comes out as follows: `X` has dimension at most one and `X'` is dense, so
  `Z = X ∖ X'` is zero-dimensional and hence a finite set of `k`-rational points; `i` is a closed
  and therefore finite immersion, so Tag 03QP and the Leray collapse of Tag 0733 identify
  `H^q(X, i_* i^{-1} F)` with `H^q(Z, i^{-1} F)`; `Z` is a disjoint union of spectra of
  algebraically closed fields, so that vanishes for `q > 0` and is the direct sum of the stalks
  `F_{x_1}, …, F_{x_n}` in degree zero; those stalks are finite because `F` is constructible; and
  the same description makes restriction along a scalar extension bijective on it. Tag 03QP is
  available at the right universe for this chain:
  `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom`
  (`@[stacks 03QP "part (2)"]`, at `AddCommGrpCat.{max (u+1) v}`). The Leray collapse of Tag 0733
  is stated for `SheafOfModules` over a ringed topos
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/LerayCollapse.lean:224`) and so is not
  usable for `Sheaf.H` on abelian sheaves, but it is not needed: for an integral `i`, and a closed
  immersion is integral, `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`
  (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ClosedPointDirectSumCohomology.lean:130`) is
  already the identification `H^q(Z, G) ≃+ H^q(X, i_* G)`; and the cohomology of the closed part is
  already computed, by `AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points`
  (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ClosedPointsVanishing.lean:208`,
  `@[stacks 09AY]`), which kills positive degrees on an affine scheme all of whose points are
  closed and all of whose residue fields are separably closed. So the field `vanishing` is within
  reach, at the universes `v = w = u + 1` where `etaleAbelianDirectImage.{u, u + 1}` and
  `Stacks.EtaleCohomology.smallEtalePushforwardAb` are the same functor; what it still needs is
  exactly the geometry density and the dimension bound are for, that `Z` is affine with all of its
  points closed and with residue fields the base field. The other two fields have no route.
  `finite_zero` needs the stalks of a constructible abelian sheaf to be finite, and this tree has
  only their torsion, by `exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf`.
  `bijective_restriction`, for the scalar extension that items (6) and (7) are about, is base
  change along an extension of algebraically closed fields, which this tree does not prove and
  states as `Stacks.EtaleCohomology.ProperBaseChangeOverAlgClosed`, an explicit input of
  `TorsionSheafSituation.properBaseChangeStatement_of_properBaseChangeOverAlgClosed` in the same
  namespace. The hypotheses of Situation 0A52 that feed only into that chain — `k` algebraically
  closed, `X` separated of finite type of dimension at most one, and `X'` dense in `X` — therefore
  do not appear below, which makes the statement correspondingly more general. This is the same
  accounting as in
  `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero`, Tag 0GJE
  with coefficients in a Noetherian ring, where the identical chain is carried as `h0` and `hpos`.
* `hprimePower` and `hprimeToChar`. Statements (3) and (6) are conditional on the coefficient
  sheaf being `l`-power torsion, resp. torsion prime to `p`, so the conclusion for one of the two
  sheaves assumes that condition for it and must supply it for the other. In the direction from
  `F` to `j_! j^{-1} F` the condition descends along the sequence above, by
  `Stacks.EtaleCohomology.isPrimePowerTorsion_of_shortExact` and
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_shortExact`, and nothing is assumed.
  In the other direction the sheaves differ exactly on `Z`, where `j_! j^{-1} F` has zero stalks
  and `F` need not, so the implication is not formal and is carried; in the source it is the
  remark that the condition is inherited both ways because the stalks of the two sheaves agree on
  the dense open and `F` is constructible.
* `hconstructible`. Statements (4) and (5) are conditional on the coefficient sheaf being
  constructible. This library's constructibility predicate for abelian sheaves,
  `AlgebraicGeometry.IsConstructibleAbelianSheaf`, is stated for the small étale site of an
  object of a `BigEtaleSite` and not for `AlgebraicGeometry.Scheme.smallEtaleTopology`, which is
  the site `CategoryTheory.Sheaf.H` and the other six statements are about, so
  `Stacks.EtaleCohomology.CurveCohomologyStatements` takes the condition as a predicate parameter.
  The transfer of that parameter between the two sheaves is `hconstructible`; in the source its
  forward half is the remark that `j_! j^{-1} F` is constructible when `F` is.

**The restriction map.** Statements (6), (7) and (8) are about
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` along a morphism `f : Y ⟶ X` left
arbitrary, as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/FiniteDirectImage.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/ShortExactExtension.lean`.
Keeping it abstract covers both uses the source makes of it, the projection of a scalar extension
in (6) and (7) and the inclusion of an open subscheme in (8), and the two sheaves of Tag 0GJA are
compared along one and the same `f`, so no quantification over `f` is needed. Statement (8) is
the one place where the eight statements interact: in the direction from `j_! j^{-1} F` to `F` the
surjectivity in degree two uses the vanishing of `H³(X, j_! j^{-1} F)`, which is statement (1) for
`j_! j^{-1} F`, and in the other direction it uses the vanishing of `H¹(Y, f^{-1} i_* i^{-1} F)`,
which comes from `ClosedComplementCohomology` through bijectivity of restriction.

Vanishing is spelled `Subsingleton`, matching Mathlib's `CategoryTheory.Sheaf.H`, which is an
`Ext`-group from the constant sheaf `ℤ` and so has no canonical zero element to compare against.
The coefficient universe is `AddCommGrpCat.{max (u + 1) v}` for schemes in `Scheme.{u}`, the
family of universes in which étale cohomology of such a scheme is computed.

## References

* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w w' v₁ v₂ u₁ u₂

namespace Stacks.EtaleCohomology

section ExtSubobject

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact) (A : C)

include hS

/-- If `Ext^{n₁}(A, -)` vanishes on the ambient object of a short exact sequence and
`Ext^{n₀}(A, -)` vanishes on the quotient, where `n₀ + 1 = n₁`, then `Ext^{n₁}(A, -)` vanishes on
the sub-object. This is the window `Ext^{n₀}(A, X₃) → Ext^{n₁}(A, X₁) → Ext^{n₁}(A, X₂)` of the
covariant long exact sequence, one place to the left of
`Stacks.EtaleCohomology.subsingleton_ext_X₂_of_shortExact`. -/
theorem subsingleton_ext_X₁_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Subsingleton (Ext.{w} A S.X₂ n₁)] [Subsingleton (Ext.{w} A S.X₃ n₀)] :
    Subsingleton (Ext.{w} A S.X₁ n₁) := by
  refine ⟨fun x y => ?_⟩
  suffices hxy : x - y = 0 by exact sub_eq_zero.mp hxy
  have hright : (x - y).comp (Ext.mk₀ S.f) (add_zero n₁) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ A hS (x - y) hright h
  rw [Subsingleton.elim a 0] at ha
  simpa using ha.symm

/-- If `Ext^{n₁}(A, -)` is finite on the ambient object of a short exact sequence and
`Ext^{n₀}(A, -)` is finite on the quotient, where `n₀ + 1 = n₁`, then `Ext^{n₁}(A, -)` is finite
on the sub-object. -/
theorem finite_ext_X₁_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Finite (Ext.{w} A S.X₂ n₁)] [Finite (Ext.{w} A S.X₃ n₀)] :
    Finite (Ext.{w} A S.X₁ n₁) :=
  (Ext.covariant_sequence_exact₁' A hS n₀ n₁ h).ab_finite

/-- In degree zero the covariant long exact sequence has no term to the left of
`Ext^0(A, X₁)`, and the transfer to the sub-object comes instead from `S.f` being a
monomorphism: `Ext^0(A, X₁)` is then a subgroup of `Ext^0(A, X₂)`. -/
theorem finite_ext_X₁_zero_of_shortExact [Finite (Ext.{w} A S.X₂ 0)] :
    Finite (Ext.{w} A S.X₁ 0) :=
  have := hS.mono_f
  Finite.of_injective _ (Ext.postcomp_mk₀_injective_of_mono A S.f)

end ExtSubobject

section SheafCohomologySubobject

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS

/-- If the degree-`n₁` sheaf cohomology of the ambient sheaf of a short exact sequence vanishes
and the degree-`n₀` cohomology of the quotient sheaf vanishes, where `n₀ + 1 = n₁`, then the
degree-`n₁` cohomology of the subsheaf vanishes. -/
theorem subsingleton_sheafCohomology_X₁_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Subsingleton (Sheaf.H.{w', w} S.X₂ n₁)] [Subsingleton (Sheaf.H.{w', w} S.X₃ n₀)] :
    Subsingleton (Sheaf.H.{w', w} S.X₁ n₁) :=
  subsingleton_ext_X₁_of_shortExact hS _ n₀ n₁ h

/-- If the degree-`n₁` sheaf cohomology of the ambient sheaf of a short exact sequence is finite
and the degree-`n₀` cohomology of the quotient sheaf is finite, where `n₀ + 1 = n₁`, then the
degree-`n₁` cohomology of the subsheaf is finite. -/
theorem finite_sheafCohomology_X₁_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Finite (Sheaf.H.{w', w} S.X₂ n₁)] [Finite (Sheaf.H.{w', w} S.X₃ n₀)] :
    Finite (Sheaf.H.{w', w} S.X₁ n₁) :=
  finite_ext_X₁_of_shortExact hS _ n₀ n₁ h

/-- In degree zero the finiteness of the cohomology of the subsheaf follows from that of the
ambient sheaf alone. -/
theorem finite_sheafCohomology_X₁_zero_of_shortExact
    [Finite (Sheaf.H.{w', w} S.X₂ 0)] :
    Finite (Sheaf.H.{w', w} S.X₁ 0) :=
  finite_ext_X₁_zero_of_shortExact hS _

end SheafCohomologySubobject

section DevissageSubobject

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

/-- The three exact windows of the covariant long exact sequence of a short exact sequence, around
`Ext^{m+1}(A, X₁)`, as exact sequences of functions. -/
private theorem function_exact_covariant_window [HasExt.{w} C] (A : C) {S : ShortComplex C}
    (hS : S.ShortExact) (m : ℕ) :
    Function.Exact ((Ext.mk₀ S.g).postcomp A (add_zero m)) (hS.extClass.postcomp A rfl :
      Ext.{w} A S.X₃ m →+ Ext.{w} A S.X₁ (m + 1)) ∧
    Function.Exact (hS.extClass.postcomp A rfl : Ext.{w} A S.X₃ m →+ Ext.{w} A S.X₁ (m + 1))
      ((Ext.mk₀ S.f).postcomp A (add_zero (m + 1))) ∧
    Function.Exact ((Ext.mk₀ S.f).postcomp A (add_zero (m + 1)))
      ((Ext.mk₀ S.g).postcomp A (add_zero (m + 1))) :=
  ⟨(ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.covariant_sequence_exact₃' A hS m (m + 1) rfl),
    (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.covariant_sequence_exact₁' A hS m (m + 1) rfl),
    (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₂' A hS (m + 1))⟩

/-- **Dévissage for bijectivity on `Ext`, towards the sub-object.** Let `G` be an exact functor
between abelian categories, `A` an object of the source and `S` a short exact sequence there. If
`G` is bijective on `Ext` from `A` into the ambient object `S.X₂` and into the quotient `S.X₃` in
every degree, then it is bijective on `Ext` from `A` into the sub-object `S.X₁` in every degree.

This is the five lemma applied to the covariant long exact sequence of `S` and the one of its
image, in the window `Ext^m(A, X₂) → Ext^m(A, X₃) → Ext^{m+1}(A, X₁) → Ext^{m+1}(A, X₂) →
Ext^{m+1}(A, X₃)`. It is `Stacks.EtaleCohomology.mapExt_bijective_of_shortExact` with the window
shifted one place to the left, and in degree zero that window runs off the end of `Ext`; there
the left-exact special case of the five lemma applies instead, its left-hand injectivity being
that of postcomposition with the monomorphism `S.f` in degree zero. -/
theorem mapExt_bijective_of_shortExact_X₁ [HasExt.{w} C] [HasExt.{w'} D] (A : C)
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ n, Function.Bijective (G.mapExtAddHom A S.X₂ n))
    (h₃ : ∀ n, Function.Bijective (G.mapExtAddHom A S.X₃ n)) (n : ℕ) :
    Function.Bijective (G.mapExtAddHom A S.X₁ n) := by
  have hS' := hS.map_of_exact G
  have := hS.mono_f
  have := hS'.mono_f
  obtain _ | m := n
  · exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      ((Ext.mk₀ S.f).postcomp A (add_zero 0))
      ((Ext.mk₀ S.g).postcomp A (add_zero 0))
      ((Ext.mk₀ (S.map G).f).postcomp (G.obj A) (add_zero 0))
      ((Ext.mk₀ (S.map G).g).postcomp (G.obj A) (add_zero 0))
      (G.mapExtAddHom A S.X₁ 0) (G.mapExtAddHom A S.X₂ 0) (G.mapExtAddHom A S.X₃ 0)
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₂' A hS 0))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.covariant_sequence_exact₂' (G.obj A) hS' 0))
      (h₂ 0) (h₃ 0).injective
      (Ext.postcomp_mk₀_injective_of_mono A S.f)
      (Ext.postcomp_mk₀_injective_of_mono (G.obj A) (S.map G).f)
  · obtain ⟨e₃, e₁, e₂⟩ := function_exact_covariant_window A hS m
    obtain ⟨e₃', e₁', e₂'⟩ := function_exact_covariant_window (G.obj A) hS' m
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      ((Ext.mk₀ S.g).postcomp A (add_zero m))
      (hS.extClass.postcomp A rfl)
      ((Ext.mk₀ S.f).postcomp A (add_zero (m + 1)))
      ((Ext.mk₀ S.g).postcomp A (add_zero (m + 1)))
      ((Ext.mk₀ (S.map G).g).postcomp (G.obj A) (add_zero m))
      (hS'.extClass.postcomp (G.obj A) rfl)
      ((Ext.mk₀ (S.map G).f).postcomp (G.obj A) (add_zero (m + 1)))
      ((Ext.mk₀ (S.map G).g).postcomp (G.obj A) (add_zero (m + 1)))
      (G.mapExtAddHom A S.X₂ m) (G.mapExtAddHom A S.X₃ m) (G.mapExtAddHom A S.X₁ (m + 1))
      (G.mapExtAddHom A S.X₂ (m + 1)) (G.mapExtAddHom A S.X₃ (m + 1))
      (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)
      e₃ e₁ e₂ e₃' e₁' e₂'
      (h₂ m).surjective (h₃ m) (h₂ (m + 1)) (h₃ (m + 1)).injective

section IsBijectiveOnExt

attribute [local instance] HasDerivedCategory.standard

/-- **Dévissage for `IsBijectiveOnExt`, towards the sub-object**, the form used below: the class
of objects into which an exact functor is bijective on `Ext` from a fixed `A` in every degree is
closed under passing to the sub-object of a short exact sequence whose quotient also lies in it.
This is `Stacks.EtaleCohomology.isBijectiveOnExt_of_shortExact` for the other outer term. -/
theorem isBijectiveOnExt_of_shortExact_X₁ (A : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ n, IsBijectiveOnExt G A S.X₂ n) (h₃ : ∀ n, IsBijectiveOnExt G A S.X₃ n) (n : ℕ) :
    IsBijectiveOnExt G A S.X₁ n := by
  have hC := HasExt.standard C
  have hD := HasExt.standard D
  refine (mapExt_bijective_iff_mapDerivedCategory G A S.X₁ n).mp
    (mapExt_bijective_of_shortExact_X₁ G A hS (fun m => ?_) (fun m => ?_) n)
  · exact (mapExt_bijective_iff_mapDerivedCategory G A S.X₂ m).mpr (h₂ m)
  · exact (mapExt_bijective_iff_mapDerivedCategory G A S.X₃ m).mpr (h₃ m)

end IsBijectiveOnExt

end DevissageSubobject

section RestrictionSubobject

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **Dévissage for the restriction map, towards the subsheaf.** Let `f : Y ⟶ X` be a morphism of
schemes and let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on the small
étale site of `X`. If restriction along `f` is bijective on étale cohomology for `F₂` and for
`F₃` in every degree, then it is bijective for `F₁` in every degree.

This is `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_shortExact` for the
subsheaf instead of the middle sheaf. Like it, it holds for an arbitrary morphism of schemes. -/
theorem etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁ (hS : S.ShortExact)
    (h₂ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₂ q))
    (h₃ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₃ q))
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₁ q) :=
  (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} f S.X₁ q).mpr
    (isBijectiveOnExt_of_shortExact_X₁ (etaleAbelianInverseImage.{u, v} f) _ hS
      (fun m =>
        (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} f S.X₂ m).mp
          (h₂ m))
      (fun m =>
        (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} f S.X₃ m).mp
          (h₃ m))
      q)

/-- **Dévissage for the restriction map, towards the subsheaf, surjectivity only.** Let
`0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on the small étale site of
`X`, let `q = r + 1`, and suppose the degree-`q` cohomology of `F₃` and the degree-`r` cohomology
of its inverse image `f^{-1} F₃` both vanish. If restriction along `f : Y ⟶ X` is surjective in
degree `q` for `F₂`, then it is surjective in degree `q` for `F₁`.

This is the counterpart for the subsheaf of
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact`, and like it
it needs a vanishing hypothesis: the class of `H^q(Y, f^{-1} F₁)` to be hit is pulled into
`H^q(Y, f^{-1} F₂)`, lifted there to `H^q(X, F₂)` by surjectivity for `F₂`, pushed down to `F₁`
using the vanishing of `H^q(X, F₃)`, and finally seen to restrict to the given class because the
two differ by a class coming from `H^r(Y, f^{-1} F₃)`. -/
theorem surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact (hS : S.ShortExact)
    (q r : ℕ) (hqr : r + 1 = q)
    (hvanishing : Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hvanishing' :
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} f).obj S.X₃) r))
    (h₂ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₂ q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₁ q) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} f)
  intro y
  obtain ⟨x₂, hx₂⟩ := h₂ (y.comp
    (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} f).map S.f)) (add_zero q))
  obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ _ hS x₂ (Subsingleton.elim _ _)
  refine ⟨x₁, ?_⟩
  have hmiddle : (etaleCohomologyRestrictionMap.{u, v, w} f S.X₁ q x₁).comp
      (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} f).map S.f)) (add_zero q) =
      y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} f).map S.f)) (add_zero q) := by
    rw [← etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} f S.f q x₁, hx₁, hx₂]
  have hz : (Ext.postcomp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} f).map S.f)) _
      (add_zero q)) (etaleCohomologyRestrictionMap.{u, v, w} f S.X₁ q x₁ - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hmiddle
  obtain ⟨z, hzeq⟩ := Ext.covariant_sequence_exact₁ _ hS' _ hz hqr
  refine sub_eq_zero.mp ?_
  rw [← hzeq, hvanishing'.elim z 0]
  simp

set_option maxHeartbeats 800000 in
/-- **The eight statements of Situation 0A52 for the middle term and for the subsheaf of a short
exact sequence agree**, once the cohomology of the quotient sheaf is known: it vanishes in
positive degrees, is finite in degree zero, and restriction along `f` is bijective on it in every
degree.

This is the whole of Stacks Project Tag 0GJA except for the identification of the sequence: for a
dense open `j : X' ⟶ X` with closed complement `i : Z ⟶ X` the sequence is
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0` and the three hypotheses on the quotient are what the
source reads off the description of `Z`. See
`Stacks.EtaleCohomology.curveCohomologyStatements_extensionByZero_iff`, where the tag is
attached.

All sixteen implications are proved from the covariant long exact sequence. Statements (1), (2)
and (3) are vanishing above a degree bound, so towards the middle sheaf the quotient contributes
in the same positive degree and towards the subsheaf one degree lower, in both cases positively;
statements (4) and (5) are finiteness in every degree, where the quotient contributes in degree
zero too; statements (6) and (7) are bijectivity of restriction in every degree, by the five
lemma in both directions; and statement (8) is surjectivity of restriction in degree two, which
towards the middle sheaf consumes statement (1) for the subsheaf in degree three and towards the
subsheaf consumes the vanishing of the degree-one cohomology of the restricted quotient.

The side conditions move as follows. Affineness in (2) and properness in (5) and (7) are
conditions on `X` and are passed along unchanged. The torsion conditions of (3), (4) and (6)
descend from the middle sheaf to the subsheaf along the sequence, by
`Stacks.EtaleCohomology.isPrimePowerTorsion_of_shortExact` and
`Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_shortExact`, and in the other direction
are carried as `hprimePower` and `hprimeToChar`. The constructibility condition of (4) and (5) is
carried in both directions as `hconstructible`. -/
theorem curveCohomologyStatements_X₂_iff_X₁_of_shortExact {k : Type u} [Field k]
    (π : X ⟶ Spec (.of k)) (l p : ℕ)
    {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    (hS : S.ShortExact)
    (hvanishing : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hfinite : Finite (Sheaf.H.{w} S.X₃ 0))
    (hrestriction : ∀ q : ℕ,
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₃ q))
    (hprimePower : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₁ →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₂)
    (hprimeToChar : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₁ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₂)
    (hconstructible : constructible S.X₁ ↔ constructible S.X₂) :
    CurveCohomologyStatements.{u, v, w} f π l p constructible S.X₂ ↔
      CurveCohomologyStatements.{u, v, w} f π l p constructible S.X₁ := by
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
    Scheme.wEqualsLocallyBijective_smallEtaleTopology X
  have hfin : ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ q) := by
    intro q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact hfinite
    · have := hvanishing q hq
      exact Finite.of_subsingleton
  have hres : ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} f).obj S.X₃) q) := by
    intro q hq
    have := hvanishing q hq
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (hrestriction q).surjective a
    obtain ⟨b', rfl⟩ := (hrestriction q).surjective b
    rw [Subsingleton.elim a' b']
  have hsub₁ : ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₂ q) →
      Subsingleton (Sheaf.H.{w} S.X₁ q) := by
    intro q hq _
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have := hvanishing m (by omega)
    exact subsingleton_sheafCohomology_X₁_of_shortExact hS m (m + 1) rfl
  have hfin₁ : ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₂ q) → Finite (Sheaf.H.{w} S.X₁ q) := by
    intro q _
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact finite_sheafCohomology_X₁_zero_of_shortExact hS
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      have := hfin m
      exact finite_sheafCohomology_X₁_of_shortExact hS m (m + 1) rfl
  have hsub₂ : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} S.X₁ q) →
      Subsingleton (Sheaf.H.{w} S.X₂ q) := by
    intro q hq _
    have := hvanishing q hq
    exact subsingleton_sheafCohomology_X₂_of_shortExact hS q
  have hfin₂ : ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₁ q) → Finite (Sheaf.H.{w} S.X₂ q) := by
    intro q _
    have := hfin q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  refine ⟨fun h => ⟨fun q hq => hsub₁ q (by omega) (h.vanishing q hq),
      fun hX q hq => hsub₁ q hq (h.vanishing_of_isAffine hX q hq),
      fun ht q hq => hsub₁ q hq (h.vanishing_of_isPrimePowerTorsion (hprimePower ht) q hq),
      fun hc ht q => hfin₁ q (h.finite_of_isPrimeToCharacteristicTorsion (hconstructible.mp hc)
        (hprimeToChar ht) q),
      fun hc hproper q => hfin₁ q (h.finite_of_isProper (hconstructible.mp hc) hproper q),
      fun ht => etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁.{u, v, w} f hS
        (h.bijective_restriction_of_isPrimeToCharacteristicTorsion (hprimeToChar ht))
        hrestriction,
      fun hproper => etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁.{u, v, w} f hS
        (h.bijective_restriction_of_isProper hproper) hrestriction,
      surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, v, w} f hS 2 1 rfl
        (hvanishing 2 (by omega)) (hres 1 (by omega)) h.surjective_restriction⟩,
    fun h => ⟨fun q hq => hsub₂ q (by omega) (h.vanishing q hq),
      fun hX q hq => hsub₂ q (by omega) (h.vanishing_of_isAffine hX q hq),
      fun ht q hq => hsub₂ q (by omega) (h.vanishing_of_isPrimePowerTorsion
        (isPrimePowerTorsion_of_shortExact l hS ht).1 q hq),
      fun hc ht q => hfin₂ q (h.finite_of_isPrimeToCharacteristicTorsion (hconstructible.mpr hc)
        (isPrimeToCharacteristicTorsion_of_shortExact p hS ht).1 q),
      fun hc hproper q => hfin₂ q (h.finite_of_isProper (hconstructible.mpr hc) hproper q),
      fun ht => etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} f hS
        (h.bijective_restriction_of_isPrimeToCharacteristicTorsion
          (isPrimeToCharacteristicTorsion_of_shortExact p hS ht).1) hrestriction,
      fun hproper => etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} f hS
        (h.bijective_restriction_of_isProper hproper) hrestriction,
      surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact.{u, v, w} f hS 2 3 rfl
        (h.vanishing 3 (by omega)) h.surjective_restriction (hrestriction 2).surjective⟩⟩

end RestrictionSubobject

section DenseOpen

variable {X X' Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X) (j : X' ⟶ X)
  [IsClosedImmersion i] [IsOpenImmersion j]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The cohomological input the closed complement of a dense open supplies.** For a closed
immersion `i : Z ⟶ X`, a morphism `f : Y ⟶ X` along which cohomology is restricted and an abelian
sheaf `F` on the small étale site of `X`: the étale cohomology of `i_* i^{-1} F` vanishes in
positive degrees, is finite in degree zero, and restriction along `f` is bijective on it in every
degree.

In Situation 0A52 with `F` constructible and `Z` the complement of a dense open, this is what the
source reads off the description of `Z` as a finite set of `k`-rational points: a closed
immersion is finite, so Tag 03QP and the Leray collapse of Tag 0733 identify
`H^q(X, i_* i^{-1} F)` with `H^q(Z, i^{-1} F)`; the latter vanishes for `q > 0` and is the direct
sum of the stalks of `F` at the points of `Z` in degree zero, finite because `F` is
constructible; and restriction along a scalar extension is bijective on that direct sum because
the points are `k`-rational. None of those steps is available in this library, so the three
conclusions are carried here rather than constructed. -/
structure ClosedComplementCohomology
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop where
  /-- The étale cohomology of `i_* i^{-1} F` vanishes in every positive degree. -/
  vanishing : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w}
    ((etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F)) q)
  /-- The étale cohomology of `i_* i^{-1} F` is finite in degree zero. -/
  finite_zero : Finite (Sheaf.H.{w}
    ((etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F)) 0)
  /-- Restriction along `f` is bijective on the étale cohomology of `i_* i^{-1} F` in every
  degree. -/
  bijective_restriction : ∀ q : ℕ, Function.Bijective
    (etaleCohomologyRestrictionMap.{u, v, w} f
      ((etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F)) q)

/-- **Stacks Project, Tag 0GJA.** Let `X` be a scheme, let `j : X' ⟶ X` be an open immersion and
let `i : Z ⟶ X` be a closed immersion onto the complement of its image, let `π` be the structure
morphism of `X` over a field, and let `F` be an abelian sheaf on the small étale site of `X`.
Then the eight statements of Situation 0A52 hold for `F` if and only if they hold for
`j_! j^{-1} F`.

Both directions come from the short exact sequence `0 → j_! j^{-1} F → F → i_* i^{-1} F → 0` of
Tag 095L: each of the eight statements is an assertion about the cohomology of one term of that
sequence, and the long exact sequence moves it between the subsheaf and the middle sheaf once the
cohomology of the closed part is known. That knowledge is `c`, which in the source is the
description of `Z` as a finite set of `k`-rational points together with constructibility of `F`.
Beyond it the proof needs the side conditions of the eight statements to move between the two
sheaves. The two conditions on the scheme, affineness in statement (2) and properness in (5) and
(7), are conditions on `X` and are passed along unchanged. The torsion conditions of statements
(3), (4) and (6) descend from `F` to the subsheaf along the sequence, and in the other direction
are carried as `hprimePower` and `hprimeToChar`; the constructibility condition of statements (4)
and (5) is carried in both directions as `hconstructible`.

The sixteen implications themselves are
`Stacks.EtaleCohomology.curveCohomologyStatements_X₂_iff_X₁_of_shortExact`, which says the same
thing for an arbitrary short exact sequence whose quotient has the cohomology `c` describes; all
this theorem adds is the sequence of Tag 095L.

This theorem does NOT prove Stacks 0GJA and carries no tag attribute. Two of its hypotheses are
false in the generality in which they are stated, so they cannot be discharged here. `f` and `j`
are independent, so `f := j` is legal, and then the sheaf `c`'s third field speaks about is zero
by `etaleAbelianInverseImageRestrictionIso` and
`isZero_etaleRestriction_etaleAbelianDirectImage`, while `H⁰(i_* i^{-1} F)` is not zero for `F`
the constant sheaf and `Z` nonempty; and for `hprimePower`, taking `X = 𝔸¹` over an algebraically
closed field of characteristic `p`, `X' = X ∖ {0}` and `F = i_*(ℤ/ℓ)` with `ℓ ≠ p`, the sheaf
`j_! j^{-1} F` is zero and so is `l`-power torsion for every `l` while `F` is not — and `F` there
is constructible, which is what the inheritance argument appeals to.

The obstruction is structural: `Stacks.EtaleCohomology.CurveCohomologyStatements` uses one
morphism for statements (6), (7) and (8), whereas the source uses two — (6) and (7) quantify over
scalar extension along an extension of algebraically closed fields (Tags 0A58, 0A59) and (8) over
restriction to an open (Tag 0A5A). The closed-complement input is true for the former and false
for the latter. Splitting those apart is the prerequisite for an unconditional 0GJA. The split
wanted is not a second free morphism parameter, though: the eight predicate definitions carrying
Tags 0A53 – 0A5A already quantify the way the source does, items (6) and (7) over the extensions
`k'/k` through `Stacks.EtaleCohomology.scalarExtensionFst` and item (8) over every open `U ⊆ X`,
so the bundling that cannot be instantiated wrongly is their conjunction over a
`Stacks.EtaleCohomology.TorsionSheafSituation`, which four of the eight already take as their only
argument.

Splitting the morphisms is not sufficient either. The residual gap is in the direction from `F` to
`j_! j^{-1} F`, for items (3), (4) and (6). For `q > 1` the sequence gives
`H^q(X, j_! j^{-1} F) ≅ H^q(X, F)`, so item (3) for `j_! j^{-1} F` comes down to the vanishing of
`H²(X, F)`, and among the eight statements for `F` only item (3) for `F` yields that — under the
hypothesis that `F` is `l`-power torsion, which does not follow from `j_! j^{-1} F` being
`l`-power torsion, by the second counterexample above. Items (4) and (6) break at the same place
on their own torsion hypotheses. What closes the gap is the assertion of items (3), (4) and (6)
for the sheaf `j_! j^{-1} F`, which is Tag 03SC and is not a consequence of the sequence: Tags
0A55, 0A56 and 0A58 are predicate *definitions* in this library
(`Stacks.EtaleCohomology.IsPrimePowerTorsionVanishing`,
`Stacks.EtaleCohomology.TorsionSheafSituation.FiniteCohomologyOfPrimeToCharacteristic` and
`Stacks.EtaleCohomology.TorsionSheafSituation.BaseChangePrimeToCharacteristic`), so applying one
of them to a second sheaf writes that assertion down and does not supply it. The source's own
justification is no wider: its remark (a) is the single implication that `j_! j^{-1} F` is torsion
prime to the characteristic when `F` is, and that serves only the direction from `j_! j^{-1} F`
to `F`. -/
theorem curveCohomologyStatements_extensionByZero_iff {k : Type u} [Field k]
    (π : X ⟶ Spec (.of k)) (l p : ℕ)
    {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (c : ClosedComplementCohomology.{u, v, w} f i F)
    (hprimePower : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F)
    (hprimeToChar : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F)
    (hconstructible : constructible
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) ↔
      constructible F) :
    CurveCohomologyStatements.{u, v, w} f π l p constructible F ↔
      CurveCohomologyStatements.{u, v, w} f π l p constructible
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F
  exact curveCohomologyStatements_X₂_iff_X₁_of_shortExact.{u, v, w} f π l p hS c.vanishing
    c.finite_zero c.bijective_restriction hprimePower hprimeToChar hconstructible

end DenseOpen

end Stacks.EtaleCohomology

end
