module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineFactor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided

/-!
# Tag 0B3V's base-change clause for the conormal isomorphism

[Stacks, Tag 0B3V] asserts, among other things, that the canonical isomorphism
`ker(q) ⊗ L^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}` of its clause (3) is compatible with base change.
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange`
reduced that assertion to one equation, the *source coherence*, and
`Stacks.ProjectiveBundleConormal.sourceCoherence` reduced the source coherence to one of its
three pieces, the *inverse-line factor*. **This file proves the inverse-line factor, and with it
the clause.**

The inverse-line factor is an equality of two composites of comparisons of tensor inverses of
`σ^*𝒪_{𝐏(ℰ)}(1)`, five factors in all. Each factor is determined by what it does to an
evaluation pairing — it is *pinned* — and the two composites are equal because the composites of
the corresponding comparisons of the *positive* lines are equal, which is
`Stacks.ProjectiveBundleConormal.positiveLine_coherence`.

## Main results

* `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_braiding` and
  `pullbackPairing_braiding`: **Tag 01CD's comparison commutes with the commutativity
  constraint of Tag 01CA**, at the scheme spelling and at the monoidal structure used here, and
  the consequence for a pulled-back pairing. This crossing is what makes both handednesses of
  the pin reachable.
* `Stacks.ProjectiveBundleConormal.invertibleEvaluation'`: the evaluation pairing of an
  invertible module in the order `L^{⊗ -1} ⊗ L`, and `invertibleEvaluation_eq`: it is one
  braiding away from `Stacks.ProjectiveBundleConormal.invertibleEvaluation`.
* `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso_pin`,
  `inverseQuotientBaseChange_pin` and `inverseTwistBundleBaseChangeIso_flip`: **the pins of the
  remaining five factors** — the two sections' inverse-line comparisons, Tag 0B3V's
  inverse-line comparison of the quotient lines, and the twist factor of `Φ` read in the
  inverse-first order.
* `Stacks.ProjBundleInverseBaseChange.negOneMulIso_eq_reseat` and
  `pullbackTensorInverse_mulIso'_eq_reseat`: the two re-seated pairings that
  `CategoryTheory.MonoidalCategory.reseat_pin` takes as hypotheses, which is where
  `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` is recognised as
  `pullbackTensorComparisonIso` and `pullbackUnitMonoidalIso` as `modulePullbackUnitIso`.
* `Stacks.ProjectiveBundleConormal.pin_comp'` and `pin_right_unique`: the composition law and
  the uniqueness for the inverse-first pin.
* `Stacks.ProjectiveBundleConormal.inverseLineFactor`: **the inverse-line factor.**
* `Stacks.ProjectiveBundleConormal.sourceCoherence_of_classifying`: the source coherence with
  `hqe` and `hqe'` in place of `hinv`.
* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange`: **the clause.**

## Handedness

A comparison `u : a⁻¹ ⟶ b⁻¹` admits two inequivalent pins along `ε : L₁ ≅ L₂`, namely
`(ε ⊗ₘ u) ≫ b.mulIso = a.mulIso` and `u ▷ L₁ ≫ b⁻¹ ◁ ε ≫ b.mulIso' = a.mulIso'`, and they
differ in where the snake identity is spent:
`Stacks.TensorPowers.TensorInverse.tensorHom_comp_mulIso_ofIso` takes the snake of its *source*
inverse and `Stacks.TensorPowers.TensorInverse.pin_invIso_ofIso` that of its *target*. In the
three `invIso`-shaped factors the source is
`Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse` and the target is a plain
`Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`, whose snake is
`negOneTensorInverse_snake`. **So the right form is the one to take**, and that is what is taken
here: every pin below has the comparison of the inverses in the *first* tensor factor.

With `pullbackPairing_braiding` the other form is no longer blocked — the crossing it needed is
paid above — but it would cost three flips rather than one, since factor 2's own pin
(`Stacks.Divisors.inverseQuotientBaseChange_evaluation`) and the pin of the comparison with Tag
01CU's `(-1)`st power both arrive inverse-first. Only factor 4 arrives in the other order, and
`flip_pin` turns it round.

`Stacks.Monoidal.eq_of_tensorHom_comp_eq`, the uniqueness recorded as the closing step, is the
uniqueness for the *other* order: it takes the known isomorphism in the first tensor factor and
the unknown in the second. `pin_right_unique` below is its mirror, and it is what closes the
assembly.

## Implementation notes

Three monoidal structures on the sheaves of modules of a scheme meet here, and each declaration
names the one it is stated over rather than leaving it to synthesis.
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is the structure used here, whose tensor
product is the tensor product sheaf of Tag 01CA; `Stacks.SheafInternalHom.monoidalCategory` is
the localized structure Tag 01CU's trivialisations live over, named here as `monoidalMods` so
that every argument is determined by the type; and `SheafOfModules.monoidalCategory` is the
structure the first is a re-seating of (`SheafOfModules.monoidalCategorySheafTensor_eq_reseat`),
named by `letI` inside the one proof that mentions it. Against this import closure,
instance search finds none of the three for the scheme spelling on its own.

Several definitional crossings are taken by `exact` against an auxiliary lemma over a bare
category rather than by `rw` or `simp`. A goal naming both `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf …)` under a `⊗` is not
type-correct at `implicit` transparency, which is where those tactics work. Each such crossing is
given its own declaration, so that the kernel meets one at a time and each has its own heartbeat
budget; `factor2Aux` takes its principal hypothesis first for the same reason, since leaving the
metavariables to be solved from the goal instead exhausts that budget.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe v u

namespace Stacks.ProjectiveBundleConormal

/-! ### Bare-category reassociations -/

/-- Moving a comparison across a pulled-back pairing, over a bare category. -/
private theorem brPairAux {D : Type u} [Category.{v} D] {P₁ P₂ P₃ P₄ P₅ P₆ : D}
    (bt : P₁ ⟶ P₂) (ciA : P₂ ⟶ P₃) (ciB : P₁ ⟶ P₄) (mb : P₄ ⟶ P₃) (mp : P₃ ⟶ P₅)
    (w : P₅ ⟶ P₆) (mbp : P₄ ⟶ P₅) (hm : mbp = mb ≫ mp) (h : ciB ≫ mb = bt ≫ ciA) :
    bt ≫ ciA ≫ mp ≫ w = ciB ≫ mbp ≫ w := by
  rw [hm, ← Category.assoc, ← h]
  simp only [Category.assoc]

/-- Cancelling a pair of mutually inverse maps off the front, over a bare category. -/
private theorem symAux {D : Type u} [Category.{v} D] {P Q R : D} (a : P ⟶ Q) (b : Q ⟶ P)
    (c : P ⟶ R) (h : a ≫ b = 𝟙 P) : a ≫ b ≫ c = c := by
  rw [← Category.assoc, h, Category.id_comp]

/-- Replacing the head and the tail of a four-arrow composite and dropping an identity,
over a bare category. The identity is passed as a hypothesis because the two objects it sits
between are equal only by `rfl`. -/
private theorem hpAux {D : Type u} [Category.{v} D] {P Q R S T₁ : D}
    (t t' : P ⟶ Q) (a : Q ⟶ R) (b : R ⟶ S) (i : S ⟶ S) (w w' : S ⟶ T₁) (m : Q ⟶ S)
    (ht : t = t') (hi : i = 𝟙 S) (hm : a ≫ b = m) (hw : w = w') :
    t ≫ a ≫ b ≫ i ≫ w = t' ≫ m ≫ w' := by
  rw [ht, hi, hw, Category.id_comp, ← hm]
  simp only [Category.assoc]

/-- A functor applied to a three-arrow composite, over a bare category. -/
private theorem mapAux {D E : Type u} [Category.{v} D] [Category.{v} E] (F : D ⥤ E)
    {P Q R S : D} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (m : P ⟶ S) (h : a ≫ b ≫ c = m) :
    F.map a ≫ F.map b ≫ F.map c = F.map m := by
  rw [← h, F.map_comp, F.map_comp]

/-- Cancelling a comparison and a unit comparison off a trivialisation, over a bare
category. -/
private theorem evalAux {D : Type u} [Category.{v} D] {P Q R S : D}
    (a : P ⟶ Q) (t : Q ⟶ P) (ev : P ⟶ R) (ui : R ⟶ S) (c : S ⟶ R) (b : Q ⟶ S)
    (ht : a ≫ t = 𝟙 P) (hu : ui ≫ c = 𝟙 R) (hb : b = t ≫ ev ≫ ui) :
    a ≫ b ≫ c = ev := by
  rw [hb]
  simp only [Category.assoc]
  rw [hu, Category.comp_id, ← Category.assoc, ht, Category.id_comp]

/-- Replacing the two outer factors of a three-arrow composite, over a bare category. -/
private theorem eqAux {D : Type u} [Category.{v} D] {P Q R S : D} (a a' : P ⟶ Q) (b : Q ⟶ R)
    (c c' : R ⟶ S) (ha : a = a') (hc : c = c') : a ≫ b ≫ c = a' ≫ b ≫ c' := by
  rw [ha, hc]

/-- The whole reassociation of the pulled-back trivialisation, over a bare category:
the two conjugating factors are replaced by their recognised forms and the middle three arrows
are contracted. -/
private theorem mulIsoAux {D : Type u} [Category.{v} D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : D}
    (p₁ : A₀ ⟶ A₃) (mn : A₃ ⟶ A₄) (p₃ : A₄ ⟶ A₇) (q : A₁ ⟶ A₆)
    (tY tY' : A₀ ⟶ A₁) (ci : A₁ ⟶ A₂) (mX : A₂ ⟶ A₃) (uX : A₄ ⟶ A₅) (pu : A₅ ⟶ A₆)
    (uY uY' : A₆ ⟶ A₇) (ev : A₂ ⟶ A₅)
    (h₁ : p₁ = tY ≫ ci ≫ mX) (h₃ : p₃ = uX ≫ pu ≫ uY) (hq : q = ci ≫ ev ≫ pu)
    (htY : tY = tY') (huY : uY = uY') (hev : mX ≫ mn ≫ uX = ev) :
    p₁ ≫ mn ≫ p₃ = tY' ≫ q ≫ uY' := by
  subst h₁
  subst h₃
  subst hq
  subst htY
  subst huY
  rw [← hev]
  simp only [Category.assoc]

/-! ### The two spellings of Tag 01CD and of the unit comparison -/

/-- Invertibility at the sheaf-condition spelling `Stacks.SheafOfModules.Invertible`'s tensor
powers are stated in, from the one `AlgebraicGeometry.Scheme.ringCatSheaf` gives. The two
spellings are equal by proof irrelevance and instance search does not cross between them. -/
local instance isInvertible_isSheaf (Z : Scheme.{u}) (M : Z.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (isSheaf_structureRingPresheaf Z) M := h

/-- **The two spellings of Tag 01CD's comparison isomorphism agree.**
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso` is a component of the
bifunctor isomorphism and `Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso` is
`CategoryTheory.asIso` of the comparison map; the forward maps are definitionally equal, and
`CategoryTheory.Iso.ext` promotes that to the isomorphisms, which is what a use of the backward
map needs. -/
theorem pullbackTensorSchemeIso_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules) :
    Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso f A B =
      pullbackTensorComparisonIso f A B :=
  Iso.ext rfl

/-- **The two spellings of the unit comparison `f^*𝒪_Z ≅ 𝒪_Y` agree.**
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which
`Stacks.ProjBundleInverseBaseChange.pullbackUnitMonoidalIso` is built from, is
`RingedSpaceModuleAdjunction.modulePullbackUnitIso`, which
`Stacks.ProjectiveBundleConormal.pullbackPairing` is built from. By `CategoryTheory.Iso.ext`,
for the reason recorded on `pullbackTensorSchemeIso_eq`. -/
theorem pullbackUnitIso_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f =
      modulePullbackUnitIso f.toLRSHom.toShHom :=
  Iso.ext rfl

section Conormal

attribute [local instance] monoidalSheafTensor symmSheafTensor

/-! ### Tag 01CD commutes with the braiding -/

/-- **The commutativity constraint of the conormal construction is the one Tag 01CD's braided
coherence is stated over.** `Stacks.PullbackTensorCoherence.braidedCategory` is
`Stacks.SheafOfModules.Strict.braidedCategory`, whose constraint is
`Stacks.SheafOfModules.tensorSheafBraiding` by `Stacks.SheafOfModules.Strict_braiding_eq`; and
that is the constraint of `SheafOfModules.symmetricCategorySheafTensor` by
`SheafOfModules.braiding_sheafTensor_eq`. The two lemmas composed are this crossing. -/
theorem braiding_eq_strict (X : Scheme.{u}) (A B : X.Modules) :
    (@BraidedCategory.braiding _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace)
        (Stacks.PullbackTensorCoherence.braidedCategory X.toRingedSpace) A B).hom =
      (β_ A B).hom :=
  (congrArg Iso.hom (Stacks.SheafOfModules.Strict_braiding_eq X.presheaf
      (isSheaf_structureRingPresheaf X) A B)).trans
    (SheafOfModules.braiding_sheafTensor_eq _ A B).symm

/-- Replacing the last factor of a two-arrow identity, over a bare category. -/
private theorem brAux {D : Type u} [Category.{v} D] {P Q R S : D}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S) (d d' : S ⟶ R)
    (h : a ≫ b = c ≫ d) (hd : d = d') : a ≫ b = c ≫ d' := by rw [h, hd]

/-- **Tag 01CD's comparison commutes with the commutativity constraint of Tag 01CA**, at the
scheme spelling and at the monoidal structure of the conormal construction.

This is `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, which is stated for
the modules of the underlying ringed space and over the strict monoidal structure, read here
through `braiding_eq_strict`. The two braidings are crossed on the source and on the target
separately, because the pullback functor and its objects are spelled differently on the two
sides and a goal naming both spellings under a `⊗` is not type-correct at `implicit`
transparency; the second crossing is therefore taken by `brAux` over a bare category.

This crossing is what the left pin of the inverse-line factor needs, and it is taken here in two
lemmas. -/
theorem pullbackTensorComparison_braiding {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    (Scheme.Modules.pullback f).map (β_ A B).hom ≫ pullbackTensorComparison f B A =
      pullbackTensorComparison f A B ≫
        (β_ ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)).hom :=
  brAux _ _ _ _ _
    ((congrArg (fun k => (Scheme.Modules.pullback f).map k ≫ pullbackTensorComparison f B A)
        (braiding_eq_strict Y A B).symm).trans
      (Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding f.toLRSHom.toShHom A B))
    (braiding_eq_strict X _ _)

/-- **The braiding crosses a pulled-back pairing.** For any pairing `p : A ⊗ B ⟶ 𝒪_Z` the braiding
of the two pulled-back factors followed by `Stacks.ProjectiveBundleConormal.pullbackPairing` of `p`
is `pullbackPairing` of the braided pairing `β_ B A ≫ p`.

This is `pullbackTensorComparison_braiding` with the comparison inverted on both sides, the
reassociation paid by `brPairAux` over a bare category. It is what lets a pin in the order
`(positive, inverse)` be read in the order `(inverse, positive)` *after* a pullback, which is
where the two handednesses of Tag 0B3V's inverse-line factor meet. -/
theorem pullbackPairing_braiding {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules)
    (p : A ⊗ B ⟶ 𝟙_ (Z.Modules)) :
    (β_ ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).obj A)).hom ≫
        pullbackPairing f A B p =
      pullbackPairing f B A ((β_ B A).hom ≫ p) := by
  have hc : (pullbackTensorComparisonIso f B A).inv ≫
        (Scheme.Modules.pullback f).map (β_ B A).hom =
      (β_ ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).obj A)).hom ≫
        (pullbackTensorComparisonIso f A B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact pullbackTensorComparison_braiding f B A
  exact brPairAux _ _ _ _ _ _ _ ((Scheme.Modules.pullback f).map_comp _ _) hc

/-! ### The evaluation pairing in the order `L^{⊗ -1} ⊗ L` -/

open Stacks.SheafOfModules.Invertible in
/-- **The evaluation pairing `L^{⊗ -1} ⊗ L ≅ 𝒪_X`**, in the order the comparison of two tensor
inverses is naturally pinned against.

`Stacks.ProjectiveBundleConormal.invertibleEvaluation` takes the two factors in the other order;
this one is the successor comparison of [Stacks, Tag 01CU] in degree `-1` followed by the
reindexing to degree `0`, whose target is the structure sheaf. The two are one braiding apart
(`braiding_comp_invertibleEvaluation`).

The tensor product is written by `@`-application rather than by the notation because its first
factor is spelled at `Stacks.SheafOfModules.TensorSheafification.structureSheaf` and the notation
resolves its monoidal structure from that factor's type. -/
def invertibleEvaluation' {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    @MonoidalCategoryStruct.tensorObj X.Modules _ _
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L ≅ 𝟙_ X.Modules :=
  tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L (-1) ≪≫
    tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (show (-1 : ℤ) + 1 = 0 by omega)

open Stacks.SheafOfModules.Invertible in
/-- **The two orders of the evaluation pairing differ by the braiding.**
`Stacks.ProjectiveBundleConormal.invertibleEvaluation` is the braiding of `L` with `L^{⊗ -1}`
followed by `invertibleEvaluation'`.

This is `Stacks.SheafOfModules.Invertible.mulNegOneIso_hom_eq` — which says Tag 01CU's
multiplication at `(1, -1)` is the braiding followed by the successor comparison and the
reindexing — with its braiding read at the commutativity constraint used here by
`SheafOfModules.braiding_sheafTensor_eq`. -/
theorem invertibleEvaluation_eq {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (invertibleEvaluation L).hom =
      (β_ L (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).hom ≫
        (invertibleEvaluation' L).hom :=
  (mulNegOneIso_hom_eq X.presheaf X.ringCatSheaf.2 L).trans
    (congrArg (fun k => k ≫ (invertibleEvaluation' L).hom)
      (SheafOfModules.braiding_sheafTensor_eq _ L
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).symm)

open Stacks.SheafOfModules.Invertible in
/-- **`invertibleEvaluation'` is the braiding followed by `invertibleEvaluation`**, which is
`invertibleEvaluation_eq` read the other way round: the two braidings cancel because the
constraint is a symmetry. Stated with the braiding named by `@`-application, for the reason
recorded on `invertibleEvaluation'`. -/
theorem braiding_comp_invertibleEvaluation {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (@BraidedCategory.braiding X.Modules _ _ _
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L).hom ≫
        (invertibleEvaluation L).hom =
      (invertibleEvaluation' L).hom :=
  (congrArg (fun k => (@BraidedCategory.braiding X.Modules _ _ _
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L).hom ≫ k)
      (invertibleEvaluation_eq L)).trans
    (symAux _ _ _ (SymmetricCategory.symmetry _ _))

/-! ### A left pin read as a right pin -/

/-- **A pin in one order is a pin in the other, against the braided pairings.** If `δ ⊗ₘ u`
carries `p₂` back to `p₁`, then `u ⊗ₘ δ` carries `β_ ≫ p₂` back to `β_ ≫ p₁`.

One `CategoryTheory.BraidedCategory.braiding_naturality`. Nothing is assumed of the pairings, and
the two braided pairings are taken as arguments with their descriptions as hypotheses, so that a
caller which has computed them in another form supplies that computation instead of rewriting
underneath a `⊗`. -/
theorem flip_pin {X : Scheme.{u}} {A A' B B' : X.Modules} (δ : A ⟶ A') (u : B ⟶ B')
    {p₁ : A ⊗ B ⟶ 𝟙_ X.Modules} {p₂ : A' ⊗ B' ⟶ 𝟙_ X.Modules}
    {q₁ : B ⊗ A ⟶ 𝟙_ X.Modules} {q₂ : B' ⊗ A' ⟶ 𝟙_ X.Modules}
    (hq₁ : q₁ = (β_ B A).hom ≫ p₁) (hq₂ : q₂ = (β_ B' A').hom ≫ p₂)
    (h : (δ ⊗ₘ u) ≫ p₂ = p₁) : (u ⊗ₘ δ) ≫ q₂ = q₁ := by
  subst hq₁
  subst hq₂
  rw [← h, ← Category.assoc, BraidedCategory.braiding_naturality]
  simp only [Category.assoc]

/-! ### Factor 4 -/

section Factor4

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **Factor 4 of the inverse-line factor, in the inverse-first order.** The twist factor of `Φ`
tensored with the comparison of the tautological twists, in the order `(𝒪(-1), 𝒪(1))`, carries
`invertibleEvaluation'` of `𝒪_{𝐏(ℰ')}(1)` back to the `h`-pullback of `invertibleEvaluation'` of
`𝒪_{𝐏(ℰ)}(1)`.

`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp` is the same pin
in the other order, against `invertibleEvaluation`; `flip_pin` exchanges the factors, and the two
braided pairings are identified by `braiding_comp_invertibleEvaluation` at the target and by
`pullbackPairing_braiding` together with it at the source. -/
theorem inverseTwistBundleBaseChangeIso_flip :
    ((inverseTwistBundleBaseChangeIso g E E' hE).hom ⊗ₘ
          (symTwistBundleBaseChangeIso g E E' hE).hom) ≫
        (invertibleEvaluation' (tautologicalTwist E' (symPieces E'))).hom =
      pullbackPairing (bundleBaseChangeHom g E E' hE) (inverseTautologicalTwist E)
        (tautologicalTwist E (symPieces E))
        (invertibleEvaluation' (tautologicalTwist E (symPieces E))).hom :=
  flip_pin _ _
    ((congrArg (pullbackPairing (bundleBaseChangeHom g E E' hE) (inverseTautologicalTwist E)
          (tautologicalTwist E (symPieces E)))
        (braiding_comp_invertibleEvaluation (tautologicalTwist E (symPieces E))).symm).trans
      (pullbackPairing_braiding (bundleBaseChangeHom g E E' hE)
        (tautologicalTwist E (symPieces E)) (inverseTautologicalTwist E) _).symm)
    (braiding_comp_invertibleEvaluation (tautologicalTwist E' (symPieces E'))).symm
    (inverseTwistBundleBaseChangeIso_tensorHom_comp g E E' hE)

end Factor4

end Conormal

end Stacks.ProjectiveBundleConormal

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.ProjectiveBundleConormal (invertibleEvaluation' pullbackPairing
  pullbackTensorSchemeIso_eq pullbackUnitIso_eq unitIso_eq)

/-- The monoidal structure Tag 01CU's trivialisations are stated over, with every argument
determined by the type so that instance search finds it. -/
@[instance_reducible] local instance monoidalMods (Z : Scheme.{u}) :
    MonoidalCategory (Mods Z) :=
  Stacks.SheafInternalHom.monoidalCategory Z.presheaf (isSheaf_structureRingPresheaf Z)

section Pairings

variable {X : Scheme.{u}} (L : Mods X)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- **`invertibleEvaluation'` in the step maps of the other development of the integer tensor
powers.** `Stacks.SheafOfModules.Invertible` and `Stacks.SheafOfModules.TensorPower` build their
successor and reindexing comparisons from their own copies of the iterate calculus;
`invertibleEvaluation'` is written in the first and
`Stacks.ProjBundleInverseBaseChange.negOneMulIso` in the second. The bridges are
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_hom_eq` and `tensorPowerReindex_eq`. -/
theorem invertibleEvaluation'_hom_eq :
    (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf
          (isSheaf_structureRingPresheaf X) L (-1)).hom ≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerReindex X.presheaf
          (isSheaf_structureRingPresheaf X) L (show (-1 : ℤ) + 1 = 0 by omega)).hom =
      (invertibleEvaluation' L).hom := by
  rw [← Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_hom_eq,
    ← congrArg Iso.hom (Stacks.SheafOfModules.Invertible.tensorPowerReindex_eq X.presheaf
      (isSheaf_structureRingPresheaf X) L (show (-1 : ℤ) + 1 = 0 by omega))]
  rfl

/-- **The right trivialisation of Tag 01CU's `(-1)`st tensor power, read at the re-seating.**
`Stacks.ProjBundleInverseBaseChange.negOneMulIso` is `invertibleEvaluation'` conjugated by
`SheafOfModules.sheafTensorIso` on its source and by `SheafOfModules.unitIso` on its target —
that is, by exactly the comparisons `CategoryTheory.MonoidalCategory.reseatIso` and `ε` of the
re-seating `SheafOfModules.monoidalCategorySheafTensor_eq_reseat` exhibits.

This is the hypothesis `hp₂` of `CategoryTheory.MonoidalCategory.reseat_pin` for the target of
every `invIso`-shaped factor of Tag 0B3V's inverse-line factor. The closing `eqToHom` of
`negOneMulIso` is the identity by proof irrelevance, and is removed by `hpAux` over a bare
category, where `exact` checks that crossing at default transparency. -/
theorem negOneMulIso_eq_reseat :
    (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom =
      (SheafOfModules.sheafTensorIso X.toRingedSpace.sheaf
          (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
            (isSheaf_structureRingPresheaf X) L (-1)) L).hom ≫
        (invertibleEvaluation' L).hom ≫
          (SheafOfModules.unitIso X.toRingedSpace.sheaf).inv :=
  Stacks.ProjectiveBundleConormal.hpAux _ _ _ _ _ _ _ _
    (congrArg Iso.hom (Stacks.ProjectiveBundleConormal.tensorIso_eq_sheafTensorIso X _ L)) rfl
    (invertibleEvaluation'_hom_eq L) (congrArg Iso.inv (unitIso_eq X))

/-- **The right trivialisation of a pulled-back tensor inverse, read at the re-seating.**
`Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`'s right trivialisation is
`Stacks.ProjectiveBundleConormal.pullbackPairing` of `invertibleEvaluation'`, conjugated by the
re-seating's two comparisons.

This is the hypothesis `hp₁` of `CategoryTheory.MonoidalCategory.reseat_pin` for the source of
every `invIso`-shaped factor of Tag 0B3V's inverse-line factor, and it is where
`pullbackTensorIso` is recognised as `pullbackTensorComparisonIso` (`pullbackTensorSchemeIso_eq`)
and `pullbackUnitMonoidalIso` as `modulePullbackUnitIso` (`pullbackUnitIso_eq`). The unit
comparison used here cancels against the one `negOneMulIso_eq_reseat` carries, and the
reassociation is paid by `mulIsoAux` over a bare category. -/
theorem pullbackTensorInverse_mulIso'_eq_reseat {Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackTensorInverse f L
        (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L)).mulIso'.hom =
      (SheafOfModules.sheafTensorIso Y.toRingedSpace.sheaf
          ((pullbackFunctor f).obj
            (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
              (isSheaf_structureRingPresheaf X) L (-1)))
          ((pullbackFunctor f).obj L)).hom ≫
        pullbackPairing f
            (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
              (isSheaf_structureRingPresheaf X) L (-1)) L
            (invertibleEvaluation' L).hom ≫
          (SheafOfModules.unitIso Y.toRingedSpace.sheaf).inv :=
  Stacks.ProjectiveBundleConormal.mulIsoAux _ _ _ _ _ _ _ _ _ _ _ _ _ (Category.assoc _ _ _) rfl
    (Stacks.ProjectiveBundleConormal.eqAux _ _ _ _ _
      (congrArg Iso.inv (pullbackTensorSchemeIso_eq f _ L)).symm
      (congrArg Iso.hom (pullbackUnitIso_eq f)).symm)
    (congrArg Iso.hom (Stacks.ProjectiveBundleConormal.tensorIso_eq_sheafTensorIso Y _ _))
    (congrArg Iso.inv (unitIso_eq Y))
    (Stacks.ProjectiveBundleConormal.mapAux (Scheme.Modules.pullback f) _ _ _ _
      (Stacks.ProjectiveBundleConormal.evalAux _ _ _ _ _ _ (Iso.inv_hom_id _)
        ((congrArg (fun k => (SheafOfModules.unitIso X.toRingedSpace.sheaf).inv ≫ k)
          (congrArg Iso.hom (unitIso_eq X))).trans (Iso.inv_hom_id _))
        (negOneMulIso_eq_reseat L)))

section Pin

attribute [local instance] Stacks.SheafInternalHom.braidedCategory

variable {Y : Scheme.{u}} (f : Y ⟶ X) (L' : Mods Y)
  [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheaf_structureRingPresheaf Y) L']
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf (isSheaf_structureRingPresheaf Y) L']

/-- **The right pin of Tag 0B3V's inverse-line comparison, at the monoidal structure Tag 01CU's
trivialisations live over.** `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso`
tensored with `hL⁻¹` and followed by the right trivialisation of `L'` is the right
trivialisation of the pulled-back inverse.

This is `Stacks.ProjBundleInverseBaseChange.pin_invIso_negOne` read through
`CategoryTheory.MonoidalCategory.tensorHom_def`, its snake hypothesis discharged by
`Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding` at `L'^{⊗ -1}`. Only the snake of the
*target* is needed, and the target is a plain `negOneTensorInverse`; that is the handedness in
which the pin has to be taken. -/
theorem inverseQuotientBaseChangeIso_pin_site (hL : L' ≅ (pullbackFunctor f).obj L) :
    ((inverseQuotientBaseChangeIso f L L' hL).hom ⊗ₘ hL.inv) ≫
        (negOneMulIso Y.presheaf (isSheaf_structureRingPresheaf Y) L').hom =
      (pullbackTensorInverse f L
        (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L)).mulIso'.hom := by
  rw [MonoidalCategory.tensorHom_def]
  exact pin_invIso_negOne Y.presheaf (isSheaf_structureRingPresheaf Y) L'
    (pullbackTensorInverse f L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L)) hL.symm
    (Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding _ _)

end Pin

end Pairings

end Stacks.ProjBundleInverseBaseChange

namespace Stacks.ProjectiveBundleConormal

open Stacks.ProjBundleInverseBaseChange (inverseQuotientBaseChangeIso negOneMulIso
  negOneTensorInverse pullbackTensorInverse negOneMulIso_eq_reseat
  pullbackTensorInverse_mulIso'_eq_reseat inverseQuotientBaseChangeIso_pin_site)

attribute [local instance] monoidalSheafTensor

section SectionPin

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E) {σ : X ⟶ (bundle E).scheme}

/-- **Factors 1 and 5 of the inverse-line factor: Tag 0B3V's identification of `σ^*𝒪(-1)` with
`(Q.L)^{⊗ -1}` is pinned along the comparison `e` of the positive lines**, at the monoidal
structure of the conormal construction.

`inverseQuotientBaseChangeIso_pin_site` is the same pin over
`Stacks.SheafInternalHom.monoidalCategory`, and
`CategoryTheory.MonoidalCategory.reseat_pin` crosses it, taking
`pullbackTensorInverse_mulIso'_eq_reseat` and `negOneMulIso_eq_reseat` as the descriptions of its
two re-seated pairings. The base monoidal structure is named by `let` inside the proof because
instance search does not find it for the scheme spelling against this import closure. -/
theorem inverseTwistBaseChangeIso_pin
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L) :
    ((inverseTwistBaseChangeIso E Q e).hom ⊗ₘ e.hom) ≫ (invertibleEvaluation' Q.L).hom =
      pullbackPairing σ (inverseTautologicalTwist E) (tautologicalTwist E (symPieces E))
        (invertibleEvaluation' (tautologicalTwist E (symPieces E))).hom :=
  by
  let : MonoidalCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) :=
    _root_.SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
  exact CategoryTheory.MonoidalCategory.reseat_pin
    (SheafOfModules.sheafTensorNatIso X.toRingedSpace.sheaf)
    (SheafOfModules.unitIso X.toRingedSpace.sheaf)
    (inverseTwistBaseChangeIso E Q e).hom e.hom
    (pullbackTensorInverse_mulIso'_eq_reseat (tautologicalTwist E (symPieces E)) σ)
    (negOneMulIso_eq_reseat Q.L)
    (inverseQuotientBaseChangeIso_pin_site (tautologicalTwist E (symPieces E)) σ Q.L e.symm)

end SectionPin

section Factor2

/-- The forward map of `RingedSpaceModuleAdjunction.modulePullbackUnitIso` is
`SheafOfModules.pullbackObjUnitToUnit`, which is the spelling
`Stacks.Divisors.inverseQuotientBaseChange_evaluation` is stated at. -/
theorem modulePullbackUnitIso_hom_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    _root_.SheafOfModules.pullbackObjUnitToUnit
        (structureSheafHom f.toLRSHom.toShHom) =
      (modulePullbackUnitIso f.toLRSHom.toShHom).hom := rfl

/-- A functor applied to a reflexive `eqToHom` is an identity and drops out. -/
private theorem headIdAux {D E : Type u} [Category.{v} D] [Category.{v} E] (F : D ⥤ E) {P : D}
    {Q : E} (h : P = P) (w w' : F.obj P ⟶ Q) (hw : w = w') : F.map (eqToHom h) ≫ w = w' := by
  rw [eqToHom_refl, F.map_id, Category.id_comp, hw]

/-- Appending an identity to a two-arrow composite, over a bare category. -/
private theorem tailIdAux {D : Type u} [Category.{v} D] {P Q R : D} (a : P ⟶ Q) (b : Q ⟶ R)
    (i : R ⟶ R) (m : P ⟶ R) (hi : i = 𝟙 R) (hm : m = a ≫ b) : m = a ≫ b ≫ i := by
  rw [hm, hi, Category.comp_id]

/-- The reassociation of factor 2's pin, over a bare category: Tag 01CD's comparison is
cancelled off the front and the two `eqToHom`s off the two tails. -/
private theorem factor2Aux {D : Type u} [Category.{v} D] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : D}
    (cmpI : P₀ ⟶ P₁) (cmp cmp' : P₁ ⟶ P₀) (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (iw w' : P₃ ⟶ P₄)
    (tm tm' : P₀ ⟶ P₅) (ev1 : P₅ ⟶ P₆) (ev2j : P₆ ⟶ P₄) (m : P₁ ⟶ P₃) (ev : P₅ ⟶ P₄)
    (hev : a ≫ b ≫ iw = cmp ≫ tm ≫ ev1 ≫ ev2j)
    (hci : cmpI ≫ cmp' = 𝟙 P₀) (hcmp : cmp = cmp') (hiw : iw = w') (hm : m = a ≫ b)
    (hev0 : ev = ev1 ≫ ev2j) (htm : tm = tm') :
    tm' ≫ ev = cmpI ≫ m ≫ w' := by
  rw [hcmp, hiw] at hev
  rw [← htm, hm, hev0]
  simp only [Category.assoc]
  rw [hev, ← Category.assoc cmpI cmp', hci, Category.id_comp]

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) (E' : X'.Modules)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)

/-- **Factor 2 of the inverse-line factor: `Stacks.Divisors.inverseQuotientBaseChange` is pinned
along `hL⁻¹`.** Tensored with `hL⁻¹` and followed by `invertibleEvaluation'` of `Q'.L`, it is the
`g`-pullback of `invertibleEvaluation'` of `Q.L`.

This factor is **not** built as `Stacks.TensorPowers.TensorInverse.invIso` but through
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne`, and its pin is
`Stacks.Divisors.inverseQuotientBaseChange_evaluation`, which is already stated in the order
`L^{⊗ -1} ⊗ L`: **no braiding is owed here.** What is owed is the bridge between the two
developments of the integer tensor powers (`invertibleEvaluation'_hom_eq`), the recognition of
Tag 01CD's comparison (`comparisonBifunctorIso_hom_app_eq`) and of the unit comparison
(`modulePullbackUnitIso_hom_eq`), the reading of the tensor product of two isomorphisms as a
`⊗ₘ` (`tensorProductIso_hom_eq_tensorHom`), and the two `eqToHom`s, which are identities by
proof irrelevance and are removed by `headIdAux` and `tailIdAux` over a bare category. -/
theorem inverseQuotientBaseChange_pin :
    ((Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL).hom ⊗ₘ hL.inv) ≫
        (invertibleEvaluation' Q'.L).hom =
      pullbackPairing g
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
        Q.L (invertibleEvaluation' Q.L).hom :=
  factor2Aux _ _ _ _ _ _ _ _ _ _ _ _ _
    (Stacks.Divisors.inverseQuotientBaseChange_evaluation g E E' Q Q' hL)
    (Iso.inv_hom_id _)
    (comparisonBifunctorIso_hom_app_eq g _ Q.L)
    (headIdAux (Scheme.Modules.pullback g) _ _ _ (modulePullbackUnitIso_hom_eq g))
    ((Scheme.Modules.pullback g).map_comp _ _)
    (tailIdAux _ _ _ _ rfl rfl)
    (tensorProductIso_hom_eq_tensorHom _ _)

end Factor2

section Assembly

/-- **Being pinned composes**, in the inverse-first order. One
`CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`; nothing is assumed of the three
pairings. This is the mirror of `Stacks.Monoidal.tensorHom_comp_eq_comp`. -/
theorem pin_comp' {X : Scheme.{u}} {A B C M N P : X.Modules}
    (u : M ⟶ N) (v : N ⟶ P) (ε : A ⟶ B) (δ : B ⟶ C)
    {hx : M ⊗ A ⟶ 𝟙_ X.Modules} {hy : N ⊗ B ⟶ 𝟙_ X.Modules} {hz : P ⊗ C ⟶ 𝟙_ X.Modules}
    (hu : (u ⊗ₘ ε) ≫ hy = hx) (hv : (v ⊗ₘ δ) ≫ hz = hy) :
    ((u ≫ v) ⊗ₘ (ε ≫ δ)) ≫ hz = hx := by
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, hv, hu]

/-- Replacing the isomorphism a pin is taken along by an equal one. -/
private theorem pinSubstAux {X : Scheme.{u}} {A B M P : X.Modules} (φ : M ⟶ P) (ε ε' : A ⟶ B)
    {p₂ : P ⊗ B ⟶ 𝟙_ X.Modules} {p₁ : M ⊗ A ⟶ 𝟙_ X.Modules}
    (hε : ε' = ε) (h : (φ ⊗ₘ ε) ≫ p₂ = p₁) : (φ ⊗ₘ ε') ≫ p₂ = p₁ := by
  rw [hε]; exact h

/-- **Being pinned in the inverse-first order determines the morphism.** Two morphisms
`M ⟶ P` pinned along the same isomorphism `ε : A ≅ B` against the same pair of pairings are
equal, provided `A` admits a tensor inverse on the right.

`Stacks.Monoidal.eq_of_tensorHom_comp_eq` is the uniqueness in the *other* order — it takes the
known isomorphism in the first tensor factor and the unknown in the second — so it does not
apply to the right pin, and this is its mirror: `CategoryTheory.MonoidalCategory.tensorHom_def`
splits the tensor product, the contraction through `ε` and `p₂` is an isomorphism and cancels,
and whiskering on the right by `A` is faithful by
`Stacks.TensorPowers.whiskerRight_injective_of_mulIso`. The hypothesis `hA` is not removable:
`p₁` and `p₂` exhibit `A` and `B` as tensor inverses on the *left*. -/
theorem pin_right_unique {X : Scheme.{u}} {A A' B M P : X.Modules}
    (hA : A ⊗ A' ≅ 𝟙_ X.Modules) (ε : A ≅ B) (p₂ : P ⊗ B ≅ 𝟙_ X.Modules)
    {p₁ : M ⊗ A ⟶ 𝟙_ X.Modules} {φ ψ : M ⟶ P}
    (hφ : (φ ⊗ₘ ε.hom) ≫ p₂.hom = p₁) (hψ : (ψ ⊗ₘ ε.hom) ≫ p₂.hom = p₁) : φ = ψ := by
  refine Stacks.TensorPowers.whiskerRight_injective_of_mulIso hA ?_
  have : IsIso (P ◁ ε.hom) := (MonoidalCategory.whiskerLeftIso P ε).isIso_hom
  have : IsIso (P ◁ ε.hom ≫ p₂.hom) := inferInstance
  have h : (φ ⊗ₘ ε.hom) ≫ p₂.hom = (ψ ⊗ₘ ε.hom) ≫ p₂.hom := hφ.trans hψ.symm
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Category.assoc,
    Category.assoc] at h
  exact (cancel_mono (P ◁ ε.hom ≫ p₂.hom)).mp h

/-- **A pairing pulled back along a morphism of schemes, as an isomorphism.** The forward map is
`Stacks.ProjectiveBundleConormal.pullbackPairing`; what the isomorphism adds is that the
pulled-back pairing again exhibits a tensor inverse, which is the hypothesis `hA` of
`pin_right_unique` at the twice-pulled-back evaluation pairing of `𝒪(1)`. -/
def pullbackPairingIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules)
    (p : A ⊗ B ≅ 𝟙_ Z.Modules) :
    (Scheme.Modules.pullback f).obj A ⊗ (Scheme.Modules.pullback f).obj B ≅ 𝟙_ Y.Modules :=
  (pullbackTensorComparisonIso f A B).symm ≪≫ (Scheme.Modules.pullback f).mapIso p ≪≫
    modulePullbackUnitIso f.toLRSHom.toShHom

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)

include hq in
/-- **The inverse-line factor of Tag 0B3V's source coherence.** The two identifications of
`g^*σ^*𝒪_{𝐏(ℰ)}(-1)` with `(Q'.L)^{⊗ -1}` agree: `g^*` of
`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` followed by
`Stacks.Divisors.inverseQuotientBaseChange`, and the square's identification followed by `σ'^*`
of the twist factor of `Φ` and `inverseTwistBaseChangeIso` downstairs.

This is the hypothesis `hinv` of `Stacks.ProjectiveBundleConormal.sourceCoherence`, and it is
**not** provable from the data that statement carries:
`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso_injective` shows its right-hand side
determines `e'`, which its left-hand side does not mention. What makes it provable is the
compatibility of the *positive* lines, `positiveLine_coherence`, whose hypotheses `hqe` and
`hqe'` — that the two sections classify the two quotients — are exactly what is added here.

Each of the five factors is pinned against an evaluation pairing in the order
`(inverse, positive)`: factors 1 and 5 by `inverseTwistBaseChangeIso_pin`, factor 2 by
`inverseQuotientBaseChange_pin`, factor 3 by
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pin` read at `invertibleEvaluation'`, and
factor 4 by `inverseTwistBundleBaseChangeIso_flip` transported along `σ'` by
`Stacks.ProjectiveBundleConormal.pullbackPairing_pin`. Being pinned composes (`pin_comp'`), so
the two sides are pinned along the two sides of `positiveLine_coherence`, and being pinned
determines the morphism (`pin_right_unique`). -/
theorem inverseLineFactor {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
      (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
        (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
          (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
      (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
        (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
          (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) :
    (Scheme.Modules.pullback g).map (inverseTwistBaseChangeIso E Q e).hom ≫
        (Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL).hom =
      (schemePullbackCompIso comm (inverseTautologicalTwist E)).hom ≫
        (Scheme.Modules.pullback σ').map (inverseTwistBundleBaseChangeIso g E E' hE).hom ≫
          (inverseTwistBaseChangeIso E' Q' e').hom := by
  have h1 := pin_comp' _ _ _ _
    (pullbackPairing_pin g _ _ _ _ (inverseTwistBaseChangeIso_pin E Q e))
    (inverseQuotientBaseChange_pin g E E' Q Q' hL)
  have h2 := pinSubstAux _ _ _
    (positiveLine_coherence g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm)
    (pin_comp' _ _ _ _
      (schemePullbackCompIso_pin comm (inverseTautologicalTwist E)
        (tautologicalTwist E (symPieces E))
        (invertibleEvaluation' (tautologicalTwist E (symPieces E))).hom)
      (pin_comp' _ _ _ _
        (pullbackPairing_pin σ' _ _ _ _ (inverseTwistBundleBaseChangeIso_flip g E E' hE))
        (inverseTwistBaseChangeIso_pin E' Q' e')))
  exact pin_right_unique
    (pullbackPairingIso g ((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)))
      ((Scheme.Modules.pullback σ).obj (inverseTautologicalTwist E))
      (pullbackPairingIso σ (tautologicalTwist E (symPieces E)) (inverseTautologicalTwist E)
        (invertibleEvaluation (tautologicalTwist E (symPieces E)))))
    ((Scheme.Modules.pullback g).mapIso e ≪≫ hL.symm) (invertibleEvaluation' Q'.L) h1 h2

include hq in
/-- **The source coherence of Tag 0B3V's base-change square, with no hypothesis beyond the data
of the two classifying sections.** This is `Stacks.ProjectiveBundleConormal.sourceCoherence` with
its inverse-line factor discharged by `inverseLineFactor`.

The conclusion is the one `sourceCoherence` has; what changes is the *shape* of the hypotheses,
`hqe` and `hqe'` in place of `hinv`. The exchange cannot be made in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceCoherence` itself, since
`inverseLineFactor` is proved here and this module imports that one; `sourceCoherence` is left as
it stands, which is the more general statement of the two. -/
theorem sourceCoherence_of_classifying {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
      (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
        (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
          (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
      (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
        (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
          (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
            (twistedSource E Q)).hom ≫
          (modulePullback σ'.toLRSHom.toShHom).map
            (twistedSourceBaseChange g E E' hE Q Q' hL hq) :=
  sourceCoherence g E E' hE Q Q' hL hq hσ e hσ' e' comm
    (inverseLineFactor g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm)

include hq in
/-- **Tag 0B3V's base-change clause for the conormal isomorphism.** For a morphism of schemes
`g : X' ⟶ X`, quasi-coherent `ℰ` on `X` and `ℰ'` on `X'` with `ℰ' ≅ g^*ℰ`, invertible quotients
`q : ℰ ⟶ L` and `q' : ℰ' ⟶ L'` identified by `hL` and `hq`, and sections `σ`, `σ'` of the two
projective bundles classifying those quotients through the comparisons `e`, `e'` of the
tautological twists and lying in a commuting square with `g`, the square

```
g^*(ker q ⊗ L^{⊗ -1}) ⟶ ker q' ⊗ (L')^{⊗ -1}
          ↓                        ↓
   g^*𝒞_{σ(X)/𝐏(ℰ)}   ⟶    𝒞_{σ'(X')/𝐏(ℰ')}
```

commutes: the left vertical is `Stacks.Divisors.conormalSourceBaseChange`, the right vertical is
`Stacks.Conormal.conormalBaseChangeMap`, and the two horizontals are
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at the two bundles.

This is
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` with
its source coherence discharged by `sourceCoherence_of_classifying`. No hypothesis beyond the data
of the square remains. -/
theorem conormalCanonicalMap_baseChange {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
      (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
        (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
          (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
      (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
        (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
          (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
    [IsImmersion σ] [IsImmersion σ']
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        conormalCanonicalMap E' Q' hσ' e' hqe' =
      (Scheme.Modules.pullback g).map (conormalCanonicalMap E Q hσ e hqe) ≫
        Stacks.Conormal.conormalBaseChangeMap comm :=
  conormalCanonicalMap_baseChange_of_twistedSourceBaseChange g E E' hE Q Q' hL hq hσ e hqe hσ' e'
    hqe' comm (sourceCoherence_of_classifying g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm)

end Assembly



end Stacks.ProjectiveBundleConormal

end
