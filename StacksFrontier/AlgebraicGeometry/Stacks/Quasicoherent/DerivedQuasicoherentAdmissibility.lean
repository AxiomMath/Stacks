module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticColocalizationTriangle
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories

/-!
# The quasi-coherent part of `D_{LQCoh^fbc}(𝒪_𝒳)` as an admissible subcategory

Let `𝒳` be an algebraic stack.  **Stacks 07BA** produces, for every object `E` of
`D_{LQCoh^fbc}(𝒪_𝒳)`, a canonical distinguished triangle `E' ⟶ E ⟶ P ⟶ E'[1]` with `P` in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `Hom(E', P') = 0` for every `P'` in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.  By the theory of admissible subcategories
([Stacks, Tag 0CQP]) this is exactly a semiorthogonal decomposition of
`D_{LQCoh^fbc}(𝒪_𝒳)`, and that is what **Stacks 0H11** records:

* `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊂ D_{LQCoh^fbc}(𝒪_𝒳)` is a *left admissible* subcategory;
* its left orthogonal `𝒜` is *right admissible* in `D_{LQCoh^fbc}(𝒪_𝒳)`;
* the composition `𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` is an equivalence, the second arrow
  being the Verdier quotient of **Stacks 07B6**;
* consequently `D_QCoh(𝒪_𝒳)` may be viewed as a strictly full saturated triangulated
  subcategory of `D_{LQCoh^fbc}(𝒪_𝒳)`, and also of `D(𝒳_{fppf}, 𝒪_𝒳)`.

## Main definitions

* `AlgebraicGeometry.Stack.derivedParasiticInLQCoh`: the subcategory
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedParasiticFreeInLQCoh`: the subcategory `𝒜` of
  `D_{LQCoh^fbc}(𝒪_𝒳)`, the left orthogonal of the previous one.
* `AlgebraicGeometry.Stack.derivedParasiticFree`: the same subcategory `𝒜`, read inside
  `D(𝒳_{fppf}, 𝒪_𝒳)`: the complexes which are locally quasi-coherent with flat base change and
  left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedParasiticFreeToLQCoh`: the inclusion of
  `AlgebraicGeometry.Stack.derivedParasiticFree` into `D_{LQCoh^fbc}(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.extensionProduct_derivedParasiticInLQCoh_eq_top`: **Stacks 07BA**
  transported from `D(𝒳_{fppf}, 𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒪_𝒳)`, i.e. the semiorthogonal
  decomposition `𝒜 ⋆ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳)`.
* **Stacks 0H11**, second assertion, is
  `AlgebraicGeometry.Stack.parasiticFreeInLQCoh_isRightAdmissible` together with
  `AlgebraicGeometry.Stack.parasiticInLQCoh_eq_rightOrthogonal`.
* **Stacks 0H11**, third assertion — the composition `𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` is
  an equivalence — is `AlgebraicGeometry.Stack.parasiticFreeInLQCoh_ι_comp_isEquivalence`.
* `AlgebraicGeometry.Stack.isSaturated_derivedParasiticFree`: **Stacks 0H11**, last assertion —
  `𝒜` read in `D(𝒳_{fppf}, 𝒪_𝒳)` is a strictly full saturated triangulated subcategory there.

## Implementation notes

### Two presentations of the ambient category

In this library `D_{LQCoh^fbc}(𝒪_𝒳)` is an `ObjectProperty` of `D(𝒳_{fppf}, 𝒪_𝒳)`, whereas
**Stacks 0H11** speaks of subcategories *of* `D_{LQCoh^fbc}(𝒪_𝒳)`.  The ambient triangulated
category here is therefore the full subcategory
`(derivedLocallyQuasicoherentFlatBaseChange ..).FullSubcategory`, which Mathlib equips with a
pretriangulated — triangulated, since `D(𝒳_{fppf}, 𝒪_𝒳)` is — structure as soon as
`D_{LQCoh^fbc}(𝒪_𝒳)` is a triangulated subcategory, and the parasitic part is
`CategoryTheory.ObjectProperty.inverseImage` along the inclusion.  The statement of
**Stacks 07BA** in this library lives in `D(𝒳_{fppf}, 𝒪_𝒳)`, so
`AlgebraicGeometry.Stack.extensionProduct_derivedParasiticInLQCoh_eq_top` transports it:
a distinguished triangle of `D(𝒳_{fppf}, 𝒪_𝒳)` all three of whose terms are locally
quasi-coherent with flat base change is the image of a distinguished triangle of the full
subcategory.  The two readings of `𝒜` are identified by
`AlgebraicGeometry.Stack.derivedParasiticFreeInLQCoh_eq_inverseImage`, which uses that
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)`, so that orthogonality against the
parasitic objects of the subcategory is orthogonality against all of them.

### The hypotheses carried, and why

Everything below is **Stacks 0H0P** applied to the output of **Stacks 07BA**, and the
hypotheses are exactly the ones under which this library has **Stacks 07BA**:

* a derived module-level lower shriek `Lsh` with an adjunction `adj : Lsh ⊣ g^*` and
  `hunit : IsIso adj.unit`, which is **Stacks 07AS** part (4) — the library has only part (3),
  for abelian sheaves, and the underived module statement **Stacks 0789** part (2);
* `hshriek`, saying that `Lg_! g^* K` is again locally quasi-coherent with flat base change,
  which is **Stacks 07B9** parts (2)(a) and (2)(c) read in succession — the library has only
  part (2)(b);
* the instances `[IsTriangulated]`, `[IsClosedUnderIsomorphisms]` on
  `D_{LQCoh^fbc}(𝒪_𝒳)` and on `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, which are **Stacks 0771** (the
  weak Serre property of `LQCoh^fbc(𝒪_𝒳)`) and **Stacks 0774** part (2), as in
  `AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW` and in
  `AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart`.

For the ambient form of the last assertion one more instance is carried,
`[IsStableUnderRetracts]` on `D_{LQCoh^fbc}(𝒪_𝒳)`: saturation of `𝒜` *inside*
`D_{LQCoh^fbc}(𝒪_𝒳)` is free, being part of [Stacks, Tag 0CQS], but saturation inside
`D(𝒳_{fppf}, 𝒪_𝒳)` also needs a direct summand of a locally quasi-coherent complex to be
locally quasi-coherent.  That is again **Stacks 0771**: for a weak Serre subcategory it is
`Stacks.DerivedCategoryB.derivedCategoryB_isStableUnderRetracts`, which is not available here
because the weak Serre property of `LQCoh^fbc(𝒪_𝒳)` is not in the library.

### What is data

The only existence assertion of the source is the equivalence
`𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)`, and it is produced as such: the composite functor is
the one named in the source, built from the inclusion
`CategoryTheory.ObjectProperty.ι` and the Verdier quotient functor
`AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherent` of **Stacks 07B6**, and the theorem
asserts `CategoryTheory.Functor.IsEquivalence` of that functor, a property of the given
functor rather than the existence of some equivalence.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 05RB](https://stacks.math.columbia.edu/tag/05RB)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks Project, Tag 0FXD](https://stacks.math.columbia.edu/tag/0FXD)
* [Stacks Project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

universe u w t t'

open FlatFppf in
attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-! ### Lifting a semiorthogonal decomposition into a full subcategory -/

section Transfer

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A distinguished triangle of `C` all three of whose terms satisfy a triangulated property `P`
is the image of a distinguished triangle of `P.FullSubcategory`.  The third morphism has to be
corrected by the commutation isomorphism of `P.ι` with the shift. -/
private lemma mem_distTriang_fullSubcategory (P : ObjectProperty C) [P.IsTriangulated]
    {X₁ X₂ X₃ : C} (h₁ : P X₁) (h₂ : P X₂) (h₃ : P X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (k : X₃ ⟶ X₁⟦(1 : ℤ)⟧) (hT : Triangle.mk f g k ∈ distTriang C) :
    Triangle.mk (homMk (X := (⟨X₁, h₁⟩ : P.FullSubcategory)) (Y := ⟨X₂, h₂⟩) f)
        (homMk (X := (⟨X₂, h₂⟩ : P.FullSubcategory)) (Y := ⟨X₃, h₃⟩) g)
        (homMk (X := (⟨X₃, h₃⟩ : P.FullSubcategory))
          (Y := (⟨X₁, h₁⟩ : P.FullSubcategory)⟦(1 : ℤ)⟧)
          (k ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨X₁, h₁⟩)) ∈
      distTriang P.FullSubcategory := by
  rw [← P.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_) <;>
    simp [Functor.mapTriangle]

/-- A functor which is a localization at a class of morphisms is a localization at any class
equal to it. -/
private lemma isLocalization_of_eq {D₁ : Type*} [Category D₁] {D₂ : Type*} [Category D₂]
    (L : D₁ ⥤ D₂) {W W' : MorphismProperty D₁} (hW : W = W') [L.IsLocalization W] :
    L.IsLocalization W' := by
  subst hW
  infer_instance

end Transfer

/-! ### The parasitic part and its left orthogonal -/

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
  [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊂ D_{LQCoh^fbc}(𝒪_𝒳)`, obtained from the
subcategory `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChange` of
`D(𝒳_{fppf}, 𝒪_𝒳)` by restricting along the inclusion of `D_{LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedParasiticInLQCoh :
    ObjectProperty
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).inverseImage
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι

/-- The subcategory `𝒜 ⊂ D_{LQCoh^fbc}(𝒪_𝒳)` of **Stacks 0H11**: the left orthogonal of
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` inside `D_{LQCoh^fbc}(𝒪_𝒳)`, that is the objects `A` of
`D_{LQCoh^fbc}(𝒪_𝒳)` with `Hom(A, P) = 0` for every parasitic `P`. -/
abbrev derivedParasiticFreeInLQCoh :
    ObjectProperty
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (derivedParasiticInLQCoh B E h S hS 𝒳).leftOrthogonal

/-- The subcategory `𝒜` of **Stacks 0H11** read inside `D(𝒳_{fppf}, 𝒪_𝒳)`: the complexes of
`𝒪_𝒳`-modules which are locally quasi-coherent with flat base change and admit no nonzero
morphism to an object of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedParasiticFree : ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).leftOrthogonal ⊓
    derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳

/-- A complex with parasitic and locally quasi-coherent cohomology is in particular locally
quasi-coherent with flat base change: `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)`. -/
private lemma derivedParasitic_le_derivedLocallyQuasicoherent :
    derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 ≤
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 :=
  fun _ hX n => (hX n).2

/-- The two readings of `𝒜` agree: an object of `D_{LQCoh^fbc}(𝒪_𝒳)` is left orthogonal to the
parasitic objects *of `D_{LQCoh^fbc}(𝒪_𝒳)`* if and only if it is left orthogonal to all
parasitic objects of `D(𝒳_{fppf}, 𝒪_𝒳)`, since every parasitic object of
`D(𝒳_{fppf}, 𝒪_𝒳)` already lies in `D_{LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedParasiticFreeInLQCoh_eq_inverseImage :
    derivedParasiticFreeInLQCoh B E h S hS 𝒳 =
      (derivedParasiticFree B E h S hS 𝒳).inverseImage
        (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι := by
  ext X
  constructor
  · refine fun hX => ⟨fun {Y} f hY => ?_, X.property⟩
    have := (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι.congr_map
      (hX (Y := ⟨Y, derivedParasitic_le_derivedLocallyQuasicoherent B E h S hS 𝒳 Y hY⟩)
        (homMk f) hY)
    simpa using this
  · exact fun hX _ f hY => ObjectProperty.hom_ext _ (hX.1 f.hom hY)

/-! ### Stacks 0H11 -/

section Main

variable [HasDerivedCategory.{t'} (FlatFppf.flatFppfModules B S hS 𝒳)]
  (Lsh : DerivedCategory (FlatFppf.flatFppfModules B S hS 𝒳) ⥤
    DerivedCategory (fppfModules B S hS 𝒳))
  (adj : Lsh ⊣ FlatFppf.derivedModuleRestriction B S hS 𝒳)
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsClosedUnderIsomorphisms]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
      𝒳).IsClosedUnderIsomorphisms]

omit [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
    𝒳).IsClosedUnderIsomorphisms] in
/-- **Stacks 07BA**, transported into `D_{LQCoh^fbc}(𝒪_𝒳)`.  Every object of
`D_{LQCoh^fbc}(𝒪_𝒳)` fits in a distinguished triangle `A ⟶ X ⟶ P ⟶ A[1]` *of*
`D_{LQCoh^fbc}(𝒪_𝒳)` with `P` parasitic and `A` in the left orthogonal `𝒜` of the parasitic
part; equivalently `𝒜 ⋆ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is all of `D_{LQCoh^fbc}(𝒪_𝒳)`.

This is literally the content of **Stacks 07BA**: the triangle produced there has its first term
in `D_{LQCoh^fbc}(𝒪_𝒳)` and left orthogonal to the parasitic part, and its third term parasitic,
hence also in `D_{LQCoh^fbc}(𝒪_𝒳)`, so all three terms lie in `D_{LQCoh^fbc}(𝒪_𝒳)` and the
triangle is the image of a distinguished triangle of the full subcategory. -/
theorem extensionProduct_derivedParasiticInLQCoh_eq_top (hunit : IsIso adj.unit)
    (hshriek : ∀ K : DerivedCategory (fppfModules B S hS 𝒳),
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K →
        derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
          (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (derivedParasiticFreeInLQCoh B E h S hS 𝒳).extensionProduct
      (derivedParasiticInLQCoh B E h S hS 𝒳) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  obtain ⟨A, P, f, g, k, hT, hA, hP⟩ :=
    FlatFppf.extensionProduct_parasiticFreePart B S hS 𝒳 Lsh adj E h hunit X.obj X.property
      (hshriek X.obj X.property)
  refine ⟨⟨A, hA.2⟩,
    ⟨P, derivedParasitic_le_derivedLocallyQuasicoherent B E h S hS 𝒳 P hP⟩,
    homMk f, homMk g, homMk (k ≫ _),
    mem_distTriang_fullSubcategory _ hA.2 X.property _ f g k hT, ?_, hP⟩
  rw [derivedParasiticFreeInLQCoh_eq_inverseImage]
  exact hA

omit [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
    𝒳).IsClosedUnderIsomorphisms] in
include adj in
/-- Condition (3) of [Stacks, Tag 0H0P] for the pair `(𝒜, D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳))` in
`D_{LQCoh^fbc}(𝒪_𝒳)`: there is no nonzero morphism from `𝒜` to the parasitic part, which holds
by definition of the left orthogonal, and every object of `D_{LQCoh^fbc}(𝒪_𝒳)` is an extension
of a parasitic object by an object of `𝒜`, which is **Stacks 07BA**. -/
private lemma semiorthogonal_derivedParasiticInLQCoh (hunit : IsIso adj.unit)
    (hshriek : ∀ K : DerivedCategory (fppfModules B S hS 𝒳),
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K →
        derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
          (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    derivedParasiticFreeInLQCoh B E h S hS 𝒳 ≤
        (derivedParasiticInLQCoh B E h S hS 𝒳).leftOrthogonal ∧
      (derivedParasiticFreeInLQCoh B E h S hS 𝒳).extensionProduct
        (derivedParasiticInLQCoh B E h S hS 𝒳) = ⊤ :=
  ⟨le_rfl, extensionProduct_derivedParasiticInLQCoh_eq_top B E h S hS 𝒳 Lsh adj hunit hshriek⟩

include adj in
/-- [Stacks, Tag 0H0P] applied to the semiorthogonal decomposition of **Stacks 07BA**, in one
go.  The three assertions of **Stacks 0H11** are extracted from this below; they are produced
together because the Verdier quotient `D_QCoh(𝒪_𝒳)` is what pins the universes of the
localization in [Stacks, Tag 0H0P]. -/
private lemma admissibility_aux (hunit : IsIso adj.unit)
    (hshriek : ∀ K : DerivedCategory (fppfModules B S hS 𝒳),
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K →
        derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
          (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (derivedParasiticInLQCoh B E h S hS 𝒳).IsLeftAdmissible ∧
      ((derivedParasiticFreeInLQCoh B E h S hS 𝒳).IsRightAdmissible ∧
        derivedParasiticInLQCoh B E h S hS 𝒳 =
          (derivedParasiticFreeInLQCoh B E h S hS 𝒳).rightOrthogonal) ∧
      ((derivedParasiticFreeInLQCoh B E h S hS 𝒳).ι ⋙
        toDerivedCategoryQuasicoherent B E h S hS 𝒳).IsEquivalence := by
  have hloc : (toDerivedCategoryQuasicoherent B E h S hS 𝒳).IsLocalization
      (derivedParasiticInLQCoh B E h S hS 𝒳).trW :=
    isLocalization_of_eq _ (derivedQuasicoherentW_eq_trW B E h S hS 𝒳)
  have hsemi := semiorthogonal_derivedParasiticInLQCoh B E h S hS 𝒳 Lsh adj hunit hshriek
  have hmain := tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp
    (derivedParasiticFreeInLQCoh B E h S hS 𝒳) (derivedParasiticInLQCoh B E h S hS 𝒳)
  have h₂ : (derivedParasiticInLQCoh B E h S hS 𝒳).IsLeftAdmissible ∧
      derivedParasiticFreeInLQCoh B E h S hS 𝒳 =
        (derivedParasiticInLQCoh B E h S hS 𝒳).leftOrthogonal :=
    (hmain.1.out 3 2).mp hsemi
  have h₁ : (derivedParasiticFreeInLQCoh B E h S hS 𝒳).IsRightAdmissible ∧
      derivedParasiticInLQCoh B E h S hS 𝒳 =
        (derivedParasiticFreeInLQCoh B E h S hS 𝒳).rightOrthogonal :=
    (hmain.1.out 3 1).mp hsemi
  exact ⟨h₂.1, h₁,
    ((hmain.2 hsemi.1 hsemi.2).1 (toDerivedCategoryQuasicoherent B E h S hS 𝒳)).1⟩

end Main

/-! ### `D_QCoh(𝒪_𝒳)` as a subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)` -/

section Ambient

variable [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsStableUnderRetracts]
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]

/-- **Stacks 0H11**, last assertion, inside `D(𝒳_{fppf}, 𝒪_𝒳)`.  The subcategory `𝒜` read in
`D(𝒳_{fppf}, 𝒪_𝒳)`, that is the locally quasi-coherent complexes with flat base change which are
left orthogonal to the parasitic ones, is a strictly full, saturated ([Stacks, Tag 05RB]),
triangulated subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)`.

Strict fullness and triangulatedness are those of a left orthogonal ([Stacks, Tag 0FXC] and
[Stacks, Tag 0CQR]) intersected with `D_{LQCoh^fbc}(𝒪_𝒳)`, and saturation is stability under
retracts of a left orthogonal, again [Stacks, Tag 0FXC], intersected with the carried stability
under retracts of `D_{LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 0H11 "the last assertion for D(𝒳_fppf, 𝒪_𝒳): 𝒜, hence D_QCoh(𝒪_𝒳), read inside \
D(𝒳_fppf, 𝒪_𝒳) is a strictly full saturated triangulated subcategory there"]
theorem isSaturated_derivedParasiticFree :
    (derivedParasiticFree B E h S hS 𝒳).IsClosedUnderIsomorphisms ∧
      (derivedParasiticFree B E h S hS 𝒳).IsSaturated ∧
      (derivedParasiticFree B E h S hS 𝒳).IsTriangulated := by
  have hortho := (isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal
    (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳)).2
  have hiso : (derivedParasiticFree B E h S hS 𝒳).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => ⟨prop_of_iso _ e hX.1, prop_of_iso _ e hX.2⟩⟩
  have hretract : (derivedParasiticFree B E h S hS 𝒳).IsStableUnderRetracts :=
    ⟨fun r hY => ⟨hortho.of_retract r hY.1,
      IsStableUnderRetracts.of_retract r hY.2⟩⟩
  exact ⟨hiso, IsSaturated.of_isStableUnderRetracts _, inferInstance⟩

/-- The inclusion `𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳)` of **Stacks 0H11**, with `𝒜` presented as the
subcategory `AlgebraicGeometry.Stack.derivedParasiticFree` of `D(𝒳_{fppf}, 𝒪_𝒳)`. -/
abbrev derivedParasiticFreeToLQCoh :
    (derivedParasiticFree B E h S hS 𝒳).FullSubcategory ⥤
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).lift
    (derivedParasiticFree B E h S hS 𝒳).ι (fun X => X.property.2)

section

variable [HasDerivedCategory.{t'} (FlatFppf.flatFppfModules B S hS 𝒳)]
  (Lsh : DerivedCategory (FlatFppf.flatFppfModules B S hS 𝒳) ⥤
    DerivedCategory (fppfModules B S hS 𝒳))
  (adj : Lsh ⊣ FlatFppf.derivedModuleRestriction B S hS 𝒳)
  [(derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
      𝒳).IsClosedUnderIsomorphisms]

end

end Ambient

end AlgebraicGeometry.Stack

end
