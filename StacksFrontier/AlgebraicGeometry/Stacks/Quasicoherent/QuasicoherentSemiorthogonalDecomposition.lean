module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSemiorthogonalDecompositionOfClass
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreAlgebraicStack

/-!
# `D_QCoh(𝒪_𝒳)` as an admissible subcategory of `D_{LQCoh^fbc}(𝒪_𝒳)` (Stacks 0H11)

Let `𝒳` be an algebraic stack. **Stacks 0H11** reads **Stacks 07BA** in the language of
admissible subcategories ([Stacks, Tag 0CQP]):

* `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊂ D_{LQCoh^fbc}(𝒪_𝒳)` is a *left admissible* subcategory;
* its left orthogonal `𝒜` is *right admissible* in `D_{LQCoh^fbc}(𝒪_𝒳)`;
* the composition `𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` is an equivalence;
* so `D_QCoh(𝒪_𝒳)` is realized as a strictly full saturated triangulated subcategory of
  `D_{LQCoh^fbc}(𝒪_𝒳)`, and also of `D(𝒳_{fppf}, 𝒪_𝒳)`.

Here `LQCoh^fbc(𝒪_𝒳)` is the class of **Stacks 0762** as the source states it,
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`, whose flat base
change maps compare with the pullback of *sheaves* on the small étale sites (**Stacks 06WC**).
`D_QCoh(𝒪_𝒳)` is the Verdier quotient of **Stacks 07B6** formed from it,
`AlgebraicGeometry.Stack.ParasiticQuotient.quotient`.

Every statement is unconditional. The inputs are:

* the derived lower shriek `Lg_!` of **Stacks 07AS** part (4),
  `AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriek`, its adjunction to restriction
  `g^*` and the invertibility of the unit, `g^* Lg_! = id`;
* **Stacks 07B9** parts (2)(a) and (2)(c): `Lg_! g^*` preserves `D_{LQCoh^fbc}(𝒪_𝒳)`,
  `AlgebraicGeometry.Stack.FlatFppf.derivedSheafFlatBaseChange_parasiticFreePart_of_single`,
  applied to **Stacks 07B3** (2) in degree `0`;
* **Stacks 0771** (2), the weak Serre property of `LQCoh^fbc(𝒪_𝒳)`, and **Stacks 0774** (2)(b),
  `AlgebraicGeometry.Stack.isSerreClass_parasiticFppfModules`, by instance search;
* [Stacks, Tag 0H0P], through the statements for an arbitrary weak Serre class in
  `AlgebraicGeometry.Stack.ParasiticQuotient`.

The derived lower shriek of **Stacks 07AS** (4) is constructed on the model
`HasDerivedCategory.standard` of `D(𝒪_𝒳)`, and the statements involving it name that model
explicitly; the saturation of `𝒜` inside `D(𝒳_{fppf}, 𝒪_𝒳)`, which does not involve `Lg_!`, is
stated for any model.

## Main results

* `AlgebraicGeometry.Stack.parasiticInLQCoh_isLeftAdmissible`: the first assertion.
* `AlgebraicGeometry.Stack.parasiticFreeInLQCoh_isRightAdmissible` and
  `AlgebraicGeometry.Stack.parasiticInLQCoh_eq_rightOrthogonal`: the second assertion.
* `AlgebraicGeometry.Stack.parasiticFreeInLQCoh_ι_comp_isEquivalence`: the third assertion.
* `AlgebraicGeometry.Stack.parasiticFreeInLQCoh_isSaturated`,
  `AlgebraicGeometry.Stack.parasiticFreeInDerivedFppf_isSaturated` and
  `AlgebraicGeometry.Stack.parasiticFreeToLQCoh_comp_isEquivalence`: the last assertion, inside
  `D_{LQCoh^fbc}(𝒪_𝒳)` and inside `D(𝒳_{fppf}, 𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
* [Stacks Project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

universe u w

open FlatFppf in
attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-- Mathlib's abelian structure on `Mod(𝒪_𝒳)`, met by instance search before the larger-universe
instances of the library, whose universe constraints it cannot solve at this site. -/
local instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Abelian (fppfModules B S hS 𝒳) :=
  SheafOfModules.instAbelian _

/-- Mathlib's abelian structure on `Mod(𝒪_{𝒳_{flat,fppf}})`; see the previous instance. -/
local instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Abelian (FlatFppf.flatFppfModules B S hS 𝒳) :=
  SheafOfModules.instAbelian _

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `LQCoh^fbc(𝒪_𝒳)` of **Stacks 0762**, with the sheaf pullback of **Stacks 06WC**. -/
local notation "𝓛" => lqcohSheafFbcFppfModules

/-- The four inputs at the actual `Lg_!`: the three assertions of **Stacks 0H11** with the derived
lower shriek of **Stacks 07AS** (4), its unit isomorphism, and **Stacks 07B9** (2)(a), (2)(c). -/
private lemma admissibility :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    (ParasiticQuotient.parasiticIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsLeftAdmissible ∧
      ((ParasiticQuotient.parasiticFreeIn B S hS 𝒳
          (𝓛 B E h S hS 𝒳)).IsRightAdmissible ∧
        ParasiticQuotient.parasiticIn B S hS 𝒳 (𝓛 B E h S hS 𝒳) =
          (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
            (𝓛 B E h S hS 𝒳)).rightOrthogonal) ∧
      ((ParasiticQuotient.parasiticFreeIn B S hS 𝒳
          (𝓛 B E h S hS 𝒳)).ι ⋙
        ParasiticQuotient.toQuotient B S hS 𝒳
          (𝓛 B E h S hS 𝒳)).IsEquivalence ∧
      (ParasiticQuotient.parasiticFreeToClass B S hS 𝒳
          (𝓛 B E h S hS 𝒳) ⋙
        ParasiticQuotient.toQuotient B S hS 𝒳
          (𝓛 B E h S hS 𝒳)).IsEquivalence := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (FlatFppf.flatFppfModules B S hS 𝒳)
  let adj := FlatFppf.derivedModuleLowerShriekAdjunction B S hS 𝒳
  have hunit := FlatFppf.isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳
  have hshriek := FlatFppf.derivedSheafFlatBaseChange_parasiticFreePart_of_single B E h S hS 𝒳
    (fun M hM p =>
      FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek
        B E h S hS 𝒳 M hM p)
  exact ⟨ParasiticQuotient.isLeftAdmissible_parasiticIn B S hS 𝒳 _ _
      adj hunit hshriek,
    ParasiticQuotient.isRightAdmissible_parasiticFreeIn B S hS 𝒳 _ _
      adj hunit hshriek,
    ParasiticQuotient.isEquivalence_parasiticFreeIn_ι_comp B S hS 𝒳 _ _
      adj hunit hshriek,
    ParasiticQuotient.isEquivalence_parasiticFreeToClass_comp B S hS 𝒳 _ _
      adj hunit hshriek⟩

/-- **Stacks 0H11**, first assertion. The subcategory
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊂ D_{LQCoh^fbc}(𝒪_𝒳)` is left admissible: a strictly full
triangulated subcategory whose inclusion has a left adjoint. -/
@[stacks 0H11 "the first assertion: D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) ⊂ D_LQCoh^fbc(𝒪_𝒳) is a \
left admissible subcategory"]
theorem parasiticInLQCoh_isLeftAdmissible :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    (ParasiticQuotient.parasiticIn B S hS 𝒳
      (𝓛 B E h S hS 𝒳)).IsLeftAdmissible :=
  (admissibility B E h S hS 𝒳).1

/-- **Stacks 0H11**, second assertion. The left orthogonal `𝒜` of
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` in `D_{LQCoh^fbc}(𝒪_𝒳)` is right admissible: a strictly full
triangulated subcategory whose inclusion has a right adjoint. -/
@[stacks 0H11 "the second assertion: the left orthogonal 𝒜 of D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) \
is right admissible in D_LQCoh^fbc(𝒪_𝒳)"]
theorem parasiticFreeInLQCoh_isRightAdmissible :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
      (𝓛 B E h S hS 𝒳)).IsRightAdmissible :=
  (admissibility B E h S hS 𝒳).2.1.1

/-- `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is the right orthogonal of its left orthogonal `𝒜`
([Stacks, Tag 0H0P]). -/
theorem parasiticInLQCoh_eq_rightOrthogonal :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    ParasiticQuotient.parasiticIn B S hS 𝒳 (𝓛 B E h S hS 𝒳) =
      (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).rightOrthogonal :=
  (admissibility B E h S hS 𝒳).2.1.2

/-- **Stacks 0H11**, third assertion. The composition

`𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)`

of the inclusion of the left orthogonal `𝒜` with the Verdier quotient functor of **Stacks 07B6**
is an equivalence of categories. -/
@[stacks 0H11 "the third assertion: the composition 𝒜 ⟶ D_LQCoh^fbc(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳) of \
the inclusion with the Verdier quotient functor of 07B6 is an equivalence"]
theorem parasiticFreeInLQCoh_ι_comp_isEquivalence :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    ((ParasiticQuotient.parasiticFreeIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).ι ⋙
      ParasiticQuotient.toQuotient B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsEquivalence :=
  (admissibility B E h S hS 𝒳).2.2.1

/-- **Stacks 0H11**, last assertion, inside `D_{LQCoh^fbc}(𝒪_𝒳)`. The left orthogonal `𝒜`, which
`AlgebraicGeometry.Stack.parasiticFreeInLQCoh_ι_comp_isEquivalence` identifies with
`D_QCoh(𝒪_𝒳)`, is a strictly full, saturated ([Stacks, Tag 05RB]), triangulated subcategory of
`D_{LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 0H11 "the last assertion for D_LQCoh^fbc(𝒪_𝒳): 𝒜, hence D_QCoh(𝒪_𝒳), is a strictly \
full saturated triangulated subcategory of D_LQCoh^fbc(𝒪_𝒳)"]
theorem parasiticFreeInLQCoh_isSaturated :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsClosedUnderIsomorphisms ∧
      (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsSaturated ∧
      (ParasiticQuotient.parasiticFreeIn B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsTriangulated := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  have := parasiticFreeInLQCoh_isRightAdmissible B E h S hS 𝒳
  have key := isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (ParasiticQuotient.parasiticFreeIn B S hS 𝒳 (𝓛 B E h S hS 𝒳))
  exact ⟨inferInstance, (key.2 (key.1.1 inferInstance)).1, inferInstance⟩

/-- **Stacks 0H11**, last assertion, inside `D(𝒳_{fppf}, 𝒪_𝒳)`. The subcategory `𝒜` read in
`D(𝒳_{fppf}, 𝒪_𝒳)` — the complexes with cohomology in `LQCoh^fbc(𝒪_𝒳)` admitting no nonzero
morphism to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` — is a strictly full, saturated, triangulated
subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)`. -/
@[stacks 0H11 "the last assertion for D(𝒳_fppf, 𝒪_𝒳): 𝒜, hence D_QCoh(𝒪_𝒳), read inside \
D(𝒳_fppf, 𝒪_𝒳) is a strictly full saturated triangulated subcategory there"]
theorem parasiticFreeInDerivedFppf_isSaturated [HasDerivedCategory (fppfModules B S hS 𝒳)] :
    (ParasiticQuotient.parasiticFree B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsClosedUnderIsomorphisms ∧
      (ParasiticQuotient.parasiticFree B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsSaturated ∧
      (ParasiticQuotient.parasiticFree B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsTriangulated :=
  ParasiticQuotient.isSaturated_parasiticFree B S hS 𝒳 _

/-- **Stacks 0H11**, the realization of `D_QCoh(𝒪_𝒳)` inside `D(𝒳_{fppf}, 𝒪_𝒳)`: the inclusion
of `𝒜`, presented as a subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)`, followed by the Verdier quotient
functor of **Stacks 07B6** is an equivalence. -/
@[stacks 0H11 "the embedding into D(𝒳_fppf, 𝒪_𝒳): the composition of the inclusion of 𝒜, \
presented as a subcategory of D(𝒳_fppf, 𝒪_𝒳), with the Verdier quotient functor of 07B6 is an \
equivalence"]
theorem parasiticFreeToLQCoh_comp_isEquivalence :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    (ParasiticQuotient.parasiticFreeToClass B S hS 𝒳
        (𝓛 B E h S hS 𝒳) ⋙
      ParasiticQuotient.toQuotient B S hS 𝒳
        (𝓛 B E h S hS 𝒳)).IsEquivalence :=
  (admissibility B E h S hS 𝒳).2.2.2

end AlgebraicGeometry.Stack
