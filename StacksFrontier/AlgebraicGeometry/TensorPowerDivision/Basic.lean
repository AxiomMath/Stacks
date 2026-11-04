module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dividing a section of `L ^⊗ (k + n)` by a nonvanishing section of `L ^⊗ k`

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `t ∈ Γ(X, L ^⊗ k)` a global section of a
tensor power and `V ⊆ X_t` an open on which `t` does not vanish. This file proves that
multiplication by `t`,

`Γ(L ^⊗ n, U) ⟶ Γ(L ^⊗ (k + n), U)`,

is **bijective** for every `U ≤ V` and every `n`, and names its inverse `a ↦ a / t`.

The `n = 0` case is the trivialization clause of [Stacks, Tag 01CY]: there `L ^⊗ 0` is the
monoidal unit and the statement is that `t` generates `L ^⊗ k` freely over `V`. Every division
already in this repository is that case — the ratio of two sections of *one and the same* power,
landing in `Γ(X, V)` (`Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf`,
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.ratio`). What is added here is the
division **across degrees**, which is what the classifying-morphism arguments around
[Stacks, Tag 01NK] need: a quotient `a / t` that is a section of `L ^⊗ n` rather than a function.

## The route

Multiplication by `t` is the morphism of sheaves of modules `Stacks.GradedSections.mulMap`, which
for a section of the `k`-th power is that section whiskered on the right by `n` copies of `L`, so
that its codomain is `L ^⊗ (k + n)` on the nose. Bijectivity on sections is proved by induction on
`n`, alternating between two descriptions:

* `n = 0`. `mulMap τ 0` is `τ` itself, and bijectivity on the sections over every open inside `X_τ`
  is the trivialization clause of [Stacks, Tag 01CY], proved as
  `Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus` for a morphism out of Mathlib's
  unit sheaf; `Stacks.SectionProduct.app_bijective_ofUnitHom` carries it to a morphism out of the
  monoidal unit, which is what a section of a tensor power is here.
* `n + 1`. `mulMap τ (n + 1)` is `mulMap τ n ▷ L`. Whiskering does **not** act on sections — the
  tensor product of sheaves of modules is a sheafification — so the step passes through stalks:
  bijectivity on the sections over every open inside `V` gives bijectivity on the stalks over `V`
  (`Stacks.SectionProduct.pstalkHom_bijective_of_app_bijective_le`), whiskering preserves that
  (`Stacks.SectionProduct.BijStalk.whiskerLeft`, and `bijStalk_whiskerRight` below by the
  braiding), and a stalkwise bijection of sheaves is bijective on the sections over every open
  inside the locus where it is stalkwise bijective
  (`TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`).

So nothing about the tensor product is computed on a section, and no restriction functor to the
open subscheme `V` is used: the whole argument stays on `X` and localises only at the stalks.

## Main definitions

* `Stacks.TensorPowerDivision.mulLinear`: multiplication by a global section `t` of `L ^⊗ k`, as a
  `Γ(X, U)`-linear map `Γ(L ^⊗ n, U) →ₗ Γ(L ^⊗ (k + n), U)`.
* `Stacks.TensorPowerDivision.mulEquiv`: the same map as a linear **equivalence**, for `U` inside
  the nonvanishing open of `t`.
* `Stacks.TensorPowerDivision.divOf`: the quotient `a / t` of a section of `L ^⊗ (k + n)` over
  `U ≤ V` by `t`.
* `Stacks.TensorPowerDivision.divTop`: the quotient of a *global* section of `L ^⊗ (k + n)` by `t`,
  as a section of `L ^⊗ n` over `V`.

## Main results

* `Stacks.TensorPowerDivision.bijective_app_mulMap`: **multiplication by a nonvanishing global
  section of `L ^⊗ k` is a bijection `Γ(L ^⊗ n, U) → Γ(L ^⊗ (k + n), U)`** for every `n` and every
  `U` inside the nonvanishing open. This is the statement the rest of the file repackages.
* `Stacks.TensorPowerDivision.mul_divOf` and `Stacks.TensorPowerDivision.divOf_eq_of_mul_eq`: the
  defining identity `(a / t) · t|_U = a` and its uniqueness;
  `Stacks.TensorPowerDivision.existsUnique_mul_eq` is the two together.
* `Stacks.TensorPowerDivision.divOf_add` and `Stacks.TensorPowerDivision.divOf_smul`: the quotient
  is `Γ(X, U)`-linear in the numerator.
* `Stacks.TensorPowerDivision.map_divOf` and `Stacks.TensorPowerDivision.map_divTop`: the quotient
  commutes with restriction to a smaller open.
* `Stacks.TensorPowerDivision.divTop_mulSections`: `(t · b) / t = b|_V`, and
  `Stacks.TensorPowerDivision.divTop_self`: `t / t = 1`.
* `Stacks.TensorPowerDivision.divTop_mulSections_cancel`: **the cancellation
  `(u · a) / (u · t) = a / t`**, for `u` a further global section of a power that does not vanish
  on `V` either. This is the nonzero-degree analogue of
  `Stacks.AlgebraicGeometry.ProjChartFullGraded.ratioOf_mul_cancel`, and it is the identity that
  makes a quotient depend only on the fraction `a / t` and not on the representative.
* `Stacks.TensorPowerDivision.bijective_mul_powCongr`: the same bijection with its codomain read
  in degree `n + k` rather than `k + n`, and `Stacks.TensorPowerDivision.divTop'`,
  `mul_divTop'`, `divTop'_eq_of_mul_eq`: the quotient of a global section of `L ^⊗ (n + k)` by
  `t`, with the same defining identity and uniqueness.

## Implementation notes

**Why the degree is `k + n` and not `n + k`.** `Stacks.GradedSections.mulMap` recurses on the
*second* exponent exactly as `Stacks.TensorPowers.natTensorPow` does, so its codomain is
`natTensorPow L (k + n)` with no transport anywhere. Writing the codomain as `L ^⊗ (n + k)` costs
one `Stacks.GradedSections.powCongr`, which is an `eqToHom`; `bijective_mul_powCongr` records that
the composite is still a bijection, and the transport is never asked to convert.

**The quotient is stated against the multiplication morphism, not against a product of sections.**
For a *local* `b` there is no global product to compare `mulMap τ n` with, so the morphism itself
is what `a / t` is characterised by. That it deserves the name "multiply by `t`" is
`Stacks.TensorPowerDivision.mulLinear_resTop`: on the restriction of a global section it is the
product `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of the graded ring of sections
of [Stacks, Tag 01CV], restricted.

**`bijective_app_iff` is `Iff.rfl`.** The clause-2 statements imported here are phrased with
`((Stacks.SectionProduct.forgetFun X).map φ).app (op U)`, the component of the underlying
presheaf-of-modules morphism, while everything below is phrased with Mathlib's
`AlgebraicGeometry.Scheme.Modules.Hom.app`. The two functions are the same term; the `Iff` exists
only so that `exact` is not asked to unify them under a `Function.Bijective`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)

## What is not done

Nothing is proved here in **negative** degree, and the obstruction is not the one the shape of
this file suggests. It is not that the multiplication is missing. The object-level addition law
`L ^⊗ a ⊗ L ^⊗ b ≅ L ^⊗ (a + b)` for integer exponents is
`Stacks.TensorPowers.TensorInverse.addIso`, so multiplication by a section `t` of `L ^⊗ k` in
integer degree is available as a morphism — the left unitor, then `t` whiskered on the right, then
`addIso` — and because that composite names the whiskering directly,
`bijStalk_whiskerRight` above would give its stalk bijectivity in one step rather than by an
induction. For the other integer power family, `Stacks.SheafOfModules.TensorPower.tensorPower`,
the morphism is even already written down, as
`Stacks.SheafOfModules.twistActionHom : F ⊗ L ^⊗ j ⟶ F ⊗ L ^⊗ (n + j)`.

What was missing when this file was written is the **nonvanishing hypothesis** in either of those
spellings: `Stacks.Ample.IsInvertibleModule` — the class
`Stacks.NonvanishingOpen.nonvanishingOpen` is defined for, and so the only class in which
`V ≤ X_t` can be said here — was available for `Stacks.Ample.tensorPowModule X L (k : ℤ)`, whose
negative powers use that family's own choice of tensor inverse, and identifying that with
`intTensorPow L h.inv k` for an arbitrary `Stacks.TensorPowers.TensorInverse h` is a comparison
this repository does not have.

**That obstruction is gone, and the integer-degree statement is proved.**
`StacksFrontier/AlgebraicGeometry/TensorPowerDivision/Integer.lean` does everything below for every
`k n : ℤ`, over the third family `Stacks.AmpleProjectiveImmersion.tensorPowerModule` — Tag 01CU's
own powers — where `Stacks.Tag01VUReduction.isInvertibleModule_tensorPowerModule` is an instance
in *every* integer degree, so `Stacks.NonvanishingOpen.nonvanishingOpen` applies to `L ^⊗ k` with
no comparison of tensor inverses at all. See `Stacks.TensorPowerDivision.intDivTop` and the
cancellation `Stacks.TensorPowerDivision.intDivTop_intMulSections_cancel`. What is not done is
only the negative half of the *natural-number* family `Stacks.TensorPowers.natTensorPow`, which
has none.

No Stacks attribute is attached to anything in this file: Tag 01CY's trivialization clause is
carried elsewhere, and what is proved here is its whiskered consequence, which is not the
statement of any tag.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules.TensorSheafification
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mulMap mul powCongr)
open Stacks.SectionProduct (globalSection BijStalk forgetFun monoidalUnitSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf mulSections globalSection_secOf
  resTop_mulSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.TensorPowerDivision

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-! ### Transfers between sections, stalks and isomorphisms -/

/-- The two spellings of the action of a morphism of `𝒪_X`-modules on the sections over `U` —
the component of the underlying morphism of presheaves of modules, and Mathlib's
`AlgebraicGeometry.Scheme.Modules.Hom.app` — are the same function. -/
theorem bijective_app_iff {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Function.Bijective (((forgetFun X).map φ).app (op U)) ↔ Function.Bijective (φ.app U) :=
  Iff.rfl

/-- An isomorphism of `𝒪_X`-modules is bijective on the sections over every open. -/
theorem bijective_app_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (U : X.Opens) :
    Function.Bijective (φ.app U) :=
  have : IsIso (φ.app U) :=
    ⟨(inv φ).app U,
      by rw [← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id, Scheme.Modules.Hom.id_app],
      by rw [← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id, Scheme.Modules.Hom.id_app]⟩
  ConcreteCategory.bijective_of_isIso _

/-- **A morphism of `𝒪_X`-modules bijective on the stalks over `W` is bijective on the sections
over every open inside `W`.** Injectivity is separatedness, surjectivity is a gluing: both halves
are `TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`, applied to the underlying
morphism of sheaves of abelian groups. -/
theorem bijective_app_of_bijStalk {M N : X.Modules} (φ : M ⟶ N) {W : X.Opens}
    (h : ∀ y ∈ W, BijStalk φ y) {U : X.Opens} (hU : U ≤ W) :
    Function.Bijective (φ.app U) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((_root_.SheafOfModules.toSheaf _).map φ) U ?_
  intro y hy
  exact h y (hU hy)

/-- **Tensoring on the right preserves bijectivity on the stalk at `x`**, for a morphism bijective
on the sections over every open inside a neighbourhood `W` of `x`. This is
`Stacks.SectionProduct.BijStalk.whiskerLeft` conjugated by the braiding, exactly as
`Stacks.SectionProduct.SurjStalk.whiskerRight` is for surjectivity. The braiding components are
not found to be isomorphisms by instance search at these monoidal spellings, so their inverses are
supplied as data through `Stacks.SectionProduct.bijStalk_of_hom_inv`. -/
theorem bijStalk_whiskerRight {M N : X.Modules} (f : M ⟶ N) (A : X.Modules) {W : X.Opens}
    {x : X} (hx : x ∈ W) (hf : ∀ U : X.Opens, U ≤ W → Function.Bijective (f.app U)) :
    BijStalk (f ▷ A) x := by
  have hb : A ◁ f = (β_ A M).hom ≫ (f ▷ A) ≫ (β_ A N).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right A f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Stacks.SectionProduct.BijStalk.of_comp_right _
    (Stacks.SectionProduct.bijStalk_of_hom_inv (β_ A N).inv_hom_id (β_ A N).hom_inv_id x) ?_
  refine Stacks.SectionProduct.BijStalk.of_comp_left _
    (Stacks.SectionProduct.bijStalk_of_hom_inv (β_ A M).hom_inv_id (β_ A M).inv_hom_id x) ?_
  exact Stacks.SectionProduct.bijStalk_congr hb
    (Stacks.SectionProduct.BijStalk.whiskerLeft A f hx hf)

/-! ### Multiplication by a nonvanishing global section -/

/-- **The trivialization clause of [Stacks, Tag 01CY] for a section read as a morphism out of the
monoidal unit.** A global section of an invertible `𝒪_X`-module is bijective on the sections over
every open inside its nonvanishing open. The library's clause is stated for a morphism out of
Mathlib's unit sheaf of modules; the re-seating is
`Stacks.SectionProduct.app_bijective_ofUnitHom`, and the two nonvanishing loci are identified by
`Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq`. -/
@[ega "0 5.5.2" "Implication b) ⇒ a)"]
theorem bijective_app_of_le_nonvanishingOpen (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (τ : 𝟙_ X.Modules ⟶ M) {W : X.Opens}
    (hW : W ≤ nonvanishingOpen X M (globalSection X M τ)) {U : X.Opens} (hU : U ≤ W) :
    Function.Bijective (τ.app U) := by
  obtain ⟨N, ⟨ψ⟩⟩ := Stacks.SectionProduct.exists_tensorSheaf_iso_unit M
  have hτ : τ = Stacks.SectionProduct.ofUnitHom
      (M.unitHomEquiv.symm (Stacks.SectionProduct.monoidalUnitHomEquiv M τ)) :=
    ((Stacks.SectionProduct.monoidalUnitHomEquiv M).symm_apply_apply τ).symm
  have hsec : Stacks.SectionProduct.monoidalUnitHomEquiv M τ
      = (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (globalSection X M τ) :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X M).eq_symm_apply.mpr rfl
  rw [hτ]
  refine (bijective_app_iff _ U).mp (Stacks.SectionProduct.app_bijective_ofUnitHom _ U ?_)
  refine Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus M N ψ _
    (W := W) (fun y hy => ?_) U hU
  rw [hsec, Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
  exact hW hy

/-- **Multiplication by a nonvanishing global section of `L ^⊗ k` is a bijection from the sections
of `L ^⊗ n` to those of `L ^⊗ (k + n)`**, over every open inside the nonvanishing open, and for
every `n`.

The induction on `n` alternates between sections and stalks: the base case is the trivialization
clause of [Stacks, Tag 01CY] and the step is `bijStalk_whiskerRight` followed by
`bijective_app_of_bijStalk`, since `Stacks.GradedSections.mulMap τ (n + 1)` is
`Stacks.GradedSections.mulMap τ n` whiskered by `L` and whiskering does not act on sections. -/
theorem bijective_app_mulMap (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {k : ℕ}
    (τ : powSections L k) {W : X.Opens}
    (hW : W ≤ nonvanishingOpen X (natTensorPow L k) (globalSection X _ τ)) :
    ∀ (n : ℕ) (U : X.Opens), U ≤ W → Function.Bijective ((mulMap τ n).app U)
  | 0, _, hU => bijective_app_of_le_nonvanishingOpen (natTensorPow L k) τ hW hU
  | n + 1, _, hU =>
      bijective_app_of_bijStalk (mulMap τ (n + 1))
        (fun _ hy => bijStalk_whiskerRight (mulMap τ n) L hy
          (bijective_app_mulMap L τ hW n)) hU

/-! ### Division across degrees -/

section Division

variable (L : X.Modules) {k : ℕ} (t : Γ(natTensorPow L k, ⊤))

/-- **Multiplication by a global section `t` of `L ^⊗ k`**, as a `Γ(X, U)`-linear map from the
sections of `L ^⊗ n` over `U` to those of `L ^⊗ (k + n)`. The degree is `k + n` on the nose: that
is the codomain `Stacks.GradedSections.mulMap` already has. -/
def mulLinear (n : ℕ) (U : X.Opens) :
    Γ(natTensorPow L n, U) →ₗ[Γ(X, U)] Γ(natTensorPow L (k + n), U) where
  toFun := (mulMap (secOf L t) n).app U
  map_add' := map_add _
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x

/-- `mulLinear L t n U` sends a section `b` of `L ^⊗ n` over `U` to
`(mulMap (secOf L t) n).app U b`. -/
@[simp] theorem mulLinear_apply (n : ℕ) (U : X.Opens) (b : Γ(natTensorPow L n, U)) :
    mulLinear L t n U b = (mulMap (secOf L t) n).app U b := rfl

/-- **On the restriction of a global section, multiplication by `t` is the product of the graded
ring of sections of [Stacks, Tag 01CV]**, restricted. -/
theorem mulLinear_resTop {n : ℕ} (b : Γ(natTensorPow L n, ⊤)) (U : X.Opens) :
    mulLinear L t n U (resTop (natTensorPow L n) b U)
      = resTop (natTensorPow L (k + n)) (mulSections L t b) U :=
  (resTop_mulSections L t b U).symm

/-- Transporting a section along `a = b` and then back along `b = a` is the identity. -/
private theorem app_powCongr_powCongr {a b : ℕ} (h : a = b) (h' : b = a) (U : X.Opens)
    (x : Γ(natTensorPow L a, U)) : (powCongr L h').app U ((powCongr L h).app U x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Stacks.GradedSections.powCongr_trans L h h' rfl, Stacks.GradedSections.powCongr_rfl,
    Scheme.Modules.Hom.id_app]
  rfl

variable [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens}
  (hV : V ≤ nonvanishingOpen X (natTensorPow L k) t)

include hV in
/-- Multiplication by `t` is bijective on sections over every open `U ≤ V`. -/
theorem bijective_mulLinear (n : ℕ) {U : X.Opens} (hU : U ≤ V) :
    Function.Bijective (mulLinear L t n U) :=
  bijective_app_mulMap L (secOf L t) (by rwa [globalSection_secOf]) n U hU

/-- **Multiplication by `t` as a linear equivalence** `Γ(L ^⊗ n, U) ≃ₗ Γ(L ^⊗ (k + n), U)`, for
`U` inside the nonvanishing open of `t`. -/
def mulEquiv (n : ℕ) {U : X.Opens} (hU : U ≤ V) :
    Γ(natTensorPow L n, U) ≃ₗ[Γ(X, U)] Γ(natTensorPow L (k + n), U) :=
  LinearEquiv.ofBijective (mulLinear L t n U) (bijective_mulLinear L t hV n hU)

/-- `mulEquiv L t hV n hU` sends a section `b` of `L ^⊗ n` over `U` to
`(mulMap (secOf L t) n).app U b`. -/
@[simp] theorem mulEquiv_apply (n : ℕ) {U : X.Opens} (hU : U ≤ V) (b : Γ(natTensorPow L n, U)) :
    mulEquiv L t hV n hU b = (mulMap (secOf L t) n).app U b := rfl

/-- **The quotient `a / t`**: the unique section of `L ^⊗ n` over `U ≤ V` whose product with `t`
is the given section `a` of `L ^⊗ (k + n)`. -/
def divOf (n : ℕ) {U : X.Opens} (hU : U ≤ V) (a : Γ(natTensorPow L (k + n), U)) :
    Γ(natTensorPow L n, U) :=
  (mulEquiv L t hV n hU).symm a

/-- **The identity that defines the quotient**: `(a / t) · t = a`. -/
theorem mul_divOf (n : ℕ) {U : X.Opens} (hU : U ≤ V) (a : Γ(natTensorPow L (k + n), U)) :
    (mulMap (secOf L t) n).app U (divOf L t hV n hU a) = a :=
  (mulEquiv L t hV n hU).apply_symm_apply a

/-- **The quotient is the unique such section.** -/
theorem divOf_eq_of_mul_eq (n : ℕ) {U : X.Opens} (hU : U ≤ V)
    {a : Γ(natTensorPow L (k + n), U)} {b : Γ(natTensorPow L n, U)}
    (h : (mulMap (secOf L t) n).app U b = a) : divOf L t hV n hU a = b := by
  rw [← h, divOf]
  exact (mulEquiv L t hV n hU).symm_apply_apply b

include hV in
/-- Existence and uniqueness of the quotient, in one statement. -/
theorem existsUnique_mul_eq (n : ℕ) {U : X.Opens} (hU : U ≤ V)
    (a : Γ(natTensorPow L (k + n), U)) :
    ∃! b : Γ(natTensorPow L n, U), (mulMap (secOf L t) n).app U b = a :=
  (bijective_mulLinear L t hV n hU).existsUnique a

/-- Dividing a product by its factor `t` returns the other factor. -/
theorem divOf_mul (n : ℕ) {U : X.Opens} (hU : U ≤ V) (b : Γ(natTensorPow L n, U)) :
    divOf L t hV n hU ((mulMap (secOf L t) n).app U b) = b :=
  divOf_eq_of_mul_eq L t hV n hU rfl

/-- The quotient is additive in the numerator. -/
theorem divOf_add (n : ℕ) {U : X.Opens} (hU : U ≤ V)
    (a a' : Γ(natTensorPow L (k + n), U)) :
    divOf L t hV n hU (a + a') = divOf L t hV n hU a + divOf L t hV n hU a' :=
  map_add (mulEquiv L t hV n hU).symm a a'

/-- The quotient is `Γ(X, U)`-linear in the numerator. -/
theorem divOf_smul (n : ℕ) {U : X.Opens} (hU : U ≤ V) (r : Γ(X, U))
    (a : Γ(natTensorPow L (k + n), U)) :
    divOf L t hV n hU (r • a) = r • divOf L t hV n hU a :=
  map_smul (mulEquiv L t hV n hU).symm r a

/-- **The quotient commutes with restriction** to a smaller open: both sides are sections whose
product with `t` is the restriction of `a`, and there is only one such. -/
theorem map_divOf (n : ℕ) {U U' : X.Opens} (hU : U ≤ V) (i : U' ⟶ U)
    (a : Γ(natTensorPow L (k + n), U)) :
    (natTensorPow L n).presheaf.map i.op (divOf L t hV n hU a)
      = divOf L t hV n (i.le.trans hU) ((natTensorPow L (k + n)).presheaf.map i.op a) := by
  refine (divOf_eq_of_mul_eq L t hV n (i.le.trans hU) ?_).symm
  have h := ConcreteCategory.congr_hom
    ((mulMap (secOf L t) n).mapPresheaf.naturality i.op) (divOf L t hV n hU a)
  simpa [mul_divOf] using h

/-- **The quotient of a global section by `t`**, as a section of `L ^⊗ n` over `V`. -/
def divTop (n : ℕ) (a : Γ(natTensorPow L (k + n), ⊤)) : Γ(natTensorPow L n, V) :=
  divOf L t hV n le_rfl (resTop (natTensorPow L (k + n)) a V)

/-- The defining identity of `divTop`: `(a / t) · t = a|_V`. -/
theorem mul_divTop (n : ℕ) (a : Γ(natTensorPow L (k + n), ⊤)) :
    (mulMap (secOf L t) n).app V (divTop L t hV n a)
      = resTop (natTensorPow L (k + n)) a V :=
  mul_divOf L t hV n le_rfl _

/-- `divTop` commutes with restriction. -/
theorem map_divTop (n : ℕ) {U : X.Opens} (i : U ⟶ V) (a : Γ(natTensorPow L (k + n), ⊤)) :
    (natTensorPow L n).presheaf.map i.op (divTop L t hV n a)
      = divOf L t hV n i.le (resTop (natTensorPow L (k + n)) a U) := by
  rw [divTop, map_divOf]
  exact congrArg (divOf L t hV n i.le) (Stacks.TensorPowerTrivialize.res_resTop _ a i)

/-- `(t · b) / t = b|_V`, for `b` a global section of `L ^⊗ n`. -/
theorem divTop_mulSections {n : ℕ} (b : Γ(natTensorPow L n, ⊤)) :
    divTop L t hV n (mulSections L t b) = resTop (natTensorPow L n) b V :=
  divOf_eq_of_mul_eq L t hV n le_rfl (mulLinear_resTop L t b V)

/-- `t / t = 1`: in degree `0` the quotient of `t` by itself is the canonical section of the
monoidal unit. -/
theorem divTop_self : divTop L t hV 0 t = monoidalUnitSection X V :=
  divOf_eq_of_mul_eq L t hV 0 le_rfl
    ((Stacks.SectionProduct.app_monoidalUnitSection_eq_map_globalSection
        (natTensorPow L k) (secOf L t) V).trans
      (congrArg (fun s : Γ(natTensorPow L k, ⊤) => resTop (natTensorPow L k) s V)
        (globalSection_secOf L t)))

/-- **The cancellation `(u · a) / (u · t) = a / t`**, for `u` a global section of a further tensor
power that does not vanish on `V` either. The nonzero-degree analogue of
`Stacks.AlgebraicGeometry.ProjChartFullGraded.ratioOf_mul_cancel`: it is what makes a quotient
depend only on the fraction and not on the representative, so it is the well-definedness input a
map out of a localization needs.

The single transport is `m + (k + n) = m + k + n`, which is where
`Stacks.GradedSections.mulMap_mul` leaves the exponents; the proof is that identity followed by
`mul_divTop` and the product formula `mulLinear_resTop`. -/
theorem divTop_mulSections_cancel {m : ℕ} (u : Γ(natTensorPow L m, ⊤))
    (hVu : V ≤ nonvanishingOpen X (natTensorPow L m) u) (n : ℕ)
    (a : Γ(natTensorPow L (k + n), ⊤)) :
    divTop L (mulSections L u t)
        ((le_inf hVu hV).trans_eq
          (Stacks.AlgebraicGeometry.ProjChartFromRatios.nonvanishingOpen_mulSections
            L u t).symm) n
        ((powCongr L (Nat.add_assoc m k n).symm).app ⊤ (mulSections L u a))
      = divTop L t hV n a := by
  refine divOf_eq_of_mul_eq L _ _ n le_rfl ?_
  have h1 : mulSections L u t = globalSection X _ (mul (secOf L u) (secOf L t)) := by
    rw [← Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_globalSection,
      globalSection_secOf, globalSection_secOf]
  have hsec : secOf L (mulSections L u t) = mul (secOf L u) (secOf L t) := by
    rw [h1, Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf_globalSection]
  rw [hsec, Stacks.GradedSections.mulMap_mul, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    mul_divTop, ← resTop_mulSections, Stacks.TensorPowerTrivialize.resTop_app]

/-! ### The same bijection written in degree `n + k` -/

include hV in
/-- **Multiplication by `t` as a bijection onto the sections of `L ^⊗ (n + k)`.** The exponents of
`Stacks.GradedSections.mulMap` come out as `k + n`; composing with the transport
`Stacks.GradedSections.powCongr`, which is an `eqToHom` and hence an isomorphism, reads the same
bijection in the other order. -/
theorem bijective_mul_powCongr (n : ℕ) {U : X.Opens} (hU : U ≤ V) :
    Function.Bijective ((mulMap (secOf L t) n ≫ powCongr L (Nat.add_comm k n)).app U) :=
  (bijective_app_of_isIso (powCongr L (Nat.add_comm k n)) U).comp
    (bijective_mulLinear L t hV n hU)

/-- **The quotient `a / t` of a global section of `L ^⊗ (n + k)`**, the degree being written in
the order a consumer coming from the graded ring `⨁_n Γ(L ^⊗ n, X)` meets it. This is `divTop`
precomposed with the transport `Stacks.GradedSections.powCongr`. -/
def divTop' (n : ℕ) (a : Γ(natTensorPow L (n + k), ⊤)) : Γ(natTensorPow L n, V) :=
  divTop L t hV n ((powCongr L (Nat.add_comm n k)).app ⊤ a)

/-- The defining identity of `divTop'`: `(a / t) · t = a|_V`, with the product read in degree
`n + k`. -/
theorem mul_divTop' (n : ℕ) (a : Γ(natTensorPow L (n + k), ⊤)) :
    (mulMap (secOf L t) n ≫ powCongr L (Nat.add_comm k n)).app V (divTop' L t hV n a)
      = resTop (natTensorPow L (n + k)) a V := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, divTop', mul_divTop,
    ← Stacks.TensorPowerTrivialize.resTop_app]
  exact congrArg (fun z : Γ(natTensorPow L (n + k), ⊤) =>
    resTop (natTensorPow L (n + k)) z V)
    (app_powCongr_powCongr L (Nat.add_comm n k) (Nat.add_comm k n) ⊤ a)

/-- `divTop'` is the unique section whose product with `t` is `a|_V`. -/
theorem divTop'_eq_of_mul_eq (n : ℕ) {a : Γ(natTensorPow L (n + k), ⊤)}
    {b : Γ(natTensorPow L n, V)}
    (h : (mulMap (secOf L t) n ≫ powCongr L (Nat.add_comm k n)).app V b
      = resTop (natTensorPow L (n + k)) a V) : divTop' L t hV n a = b := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  refine divOf_eq_of_mul_eq L t hV n le_rfl ?_
  rw [Stacks.TensorPowerTrivialize.resTop_app]
  exact (app_powCongr_powCongr L (Nat.add_comm k n) (Nat.add_comm n k) V _).symm.trans
    (congrArg ((powCongr L (Nat.add_comm n k)).app V) h)

end Division

end Stacks.TensorPowerDivision

end
