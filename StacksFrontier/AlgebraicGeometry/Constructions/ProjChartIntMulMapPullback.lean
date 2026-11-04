module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackMul
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict

/-!
# Multiplication by a section of an integer tensor power commutes with pullback

Let `j : Y' ⟶ Y` be a morphism of schemes, `L` an invertible `𝒪_Y`-module and `t` a global
section of `L ^⊗ k` in an integer degree. Multiplication by `t` is the morphism
`Stacks.TensorPowerDivision.intMulMap`, and this file proves that the canonical comparison of the
integer tensor powers under pullback intertwines it with multiplication by the pullback of `t`:

  `j^*(intMulMap t n) ≫ c (k + n) = c n ≫ intMulMap (j^*t) n`,

in **every** pair of integer degrees and with **no hypothesis**. This is the hypothesis `hmul`
carried through `StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntDivisionPullback`,
whose `intDivTop_intPullSection` therefore becomes unconditional for this family —
`intDivTop_intCompare` below.

## The shape of the argument

`intMulMap L τ n` is `(λ_).inv ≫ (τ ▷ L ^⊗ n) ≫ (intMulIso L k n).hom`, so three identities are
composed, all in the localized monoidal structure `Stacks.SheafInternalHom.schemeMonoidalCategory`
that `Stacks.TensorPowerDivision` is written in:

* the multiplicativity of the comparison, which is
  `Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso_intMulIso`, proved with no
  hypothesis;
* naturality of the cotensorator of `j^*` in its **first** slot, which is
  `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator_whiskerRight`;
* the left unit law of that cotensorator, which is
  `Stacks.TensorSheafSpellingIso.pullbackCotensorator_leftUnitor`;

together with `Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.intSecOf_intPullSection`,
which reads the pulled-back section as a morphism out of the unit, and the monoidal bookkeeping
`CategoryTheory.MonoidalCategory.tensorHom_def`, `comp_whiskerRight`, `whisker_exchange` and
`leftUnitor_naturality`.

## Why the two cotensorators have to be identified

The multiplicativity square is stated against
`Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intCotensor`, which is [Stacks, Tag 01CD]'s
comparison conjugated by `Stacks.SheafOfModules.tensorObjIso`; the naturality and unit laws are
stated against `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator`,
which is the same comparison conjugated by
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`. Those two isomorphisms are the same morphism
(`Stacks.TensorSheafSpellingIso.tensorIsoTensorModules_eq`) but not the same `Iso` record, so the
two cotensorators are *not* equal by `rfl` — `pullbackCotensorator_eq_intCotensor` below crosses
that once, and nothing downstream has to.

## Main definitions

* `…intCompare`: **the canonical comparison family** `j^*(L ^⊗ d) ⟶ (j^*L) ^⊗ d`, `d : ℤ`, as an
  element of `Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.IntCompare`.

## Main results

* `…pullbackCotensorator_eq_intCotensor`: the two spellings of the cotensorator agree.
* `…intCompare_intMulMap`: **the intertwining, unconditionally** — the hypothesis `hmul`.
* `…intPullSectionOn_app_intMulMap` and `…intDivTop_intPullSection`: the two consequences in
  `ProjChartIntDivisionPullback`, with `hmul` discharged.

## Implementation notes

`rw` and `simp` do not act on the categorical structure here, for the reason recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackMul`:
`AlgebraicGeometry.Scheme.Modules` is a `def`, and not even `CategoryTheory.Category.assoc`
matches a goal that prints character-identically to its statement. So every ingredient is
taken as a `have` — which resolves its monoidal instance at the *application*, from the
declaration's own baked-in instance, and so needs no instance to be active here — and the whole
reassociation is done by `bigAssemble`, stated over an abstract category with **every object a
variable**. Taking the ingredients as `have`s is also what makes the strict monoidal structure
usable from inside a section where the localized one is active: nothing below ever *writes* a
strict whiskering.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.TensorPowerDivision (intMulIso intMulMap intSecOf)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso intCotensor
  intPullIso_intMulIso)
open Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback (IntCompare intPullSection
  intPullSectionOn intSecOf_intPullSection)
open Stacks.TensorPowerDivision (intDivTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackCotensorator_eq pullbackCotensorator_whiskerRight)
open Stacks.TensorSheafSpellingIso (tensorIsoTensorModules_eq pullbackCotensorator_leftUnitor)
open Stacks.AmplePullbackPart1 (tensorIsoTensorModules)
open Stacks.PullbackUnitSection (unitPullback unitPullbackHom unitPullbackIso)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.stacksInvertible

/-! ### Pure category theory, with every object a variable -/

/-- Replacing the outer two factors of a three-fold composite by equal morphisms. Used to turn
the cotensorator of `…ProjChartPullbackCotensorator` into the one of `…ProjChartIntPullbackMul`
without naming either object. -/
private theorem rebuild {C : Type*} [Category C] {P Q R S : C} {a a' : P ⟶ Q} {b : Q ⟶ R}
    {c c' : R ⟶ S} (ha : a = a') (hc : c = c') : a ≫ b ≫ c = a' ≫ b ≫ c' := by
  rw [ha, hc]

/-- Cancelling a retraction off the front of a composite. -/
private theorem cancelFront {C : Type*} [Category C] {P Q R : C} {a : P ⟶ Q} {b : Q ⟶ P}
    (hab : a ≫ b = 𝟙 P) (c : P ⟶ R) : a ≫ b ≫ c = c := by
  rw [← Category.assoc, hab, Category.id_comp]

/-- The left unit law of the cotensorator, composed with the inverse unitor upstairs: the
pullback of `(λ_).inv` cancels the three factors the unit law produces. -/
private theorem peelUnitor {C : Type*} [Category C] {A1 A2 A8 A12 : C} (li : A1 ⟶ A2)
    (lh : A2 ⟶ A1) (c1 : A2 ⟶ A8) (wuph : A8 ⟶ A12) (lam : A12 ⟶ A1)
    (hf : lh = c1 ≫ wuph ≫ lam) (hk : li ≫ lh = 𝟙 A1) : li ≫ c1 ≫ wuph ≫ lam = 𝟙 A1 := by
  rwa [← hf]

/-- Naturality of the left unitor read backwards: whiskering the comparison into the unit is
the unitor, the comparison and the inverse unitor in turn. -/
private theorem peelWhisker {C : Type*} [Category C] {A1 A9 A10 A12 : C} (lam : A12 ⟶ A1)
    (ipn : A1 ⟶ A9) (iv : A9 ⟶ A10) (lmh : A10 ⟶ A9) (wipn : A12 ⟶ A10)
    (hg : wipn ≫ lmh = lam ≫ ipn) (hl : lmh ≫ iv = 𝟙 A10) : wipn = lam ≫ ipn ≫ iv := by
  rw [← Category.assoc, ← hg, Category.assoc, hl, Category.comp_id]

/-- **The whole reassociation of the multiplicativity identity, as pure category theory with
every object a variable.** The nine hypotheses are, in order: the multiplicativity of the
comparison, the first-slot naturality of the cotensorator, `tensorHom_def`, the two right
whiskerings meeting at the pulled-back section, `whisker_exchange`, the left unit law of the
cotensorator, naturality of the left unitor, and the two cancellations `λ_.hom ≫ λ_.inv = 𝟙` and
`j^*(λ_).inv ≫ j^*(λ_).hom = 𝟙`. Stated here rather than inline because `rw` and `simp` do not
act on the categorical structure at the scheme spelling, and do act on this one. -/
private theorem bigAssemble {C : Type*} [Category C]
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : C}
    {li : A1 ⟶ A2} {lh : A2 ⟶ A1} {wt : A2 ⟶ A3} {mm : A3 ⟶ A4} {ikn : A4 ⟶ A5}
    {c2 : A3 ⟶ A6} {th : A6 ⟶ A7} {mu : A7 ⟶ A5} {c1 : A2 ⟶ A8} {wpt : A8 ⟶ A6}
    {wikr : A6 ⟶ A11} {wln : A11 ⟶ A7} {wuph : A8 ⟶ A12} {lam : A12 ⟶ A1}
    {ipn : A1 ⟶ A9} {iv : A9 ⟶ A10} {lmh : A10 ⟶ A9} {wtau : A10 ⟶ A7}
    {wipn : A12 ⟶ A10} {wtau2 : A12 ⟶ A11}
    (hb : mm ≫ ikn = c2 ≫ th ≫ mu) (hc : wt ≫ c2 = c1 ≫ wpt) (hd : th = wikr ≫ wln)
    (hei : wpt ≫ wikr = wuph ≫ wtau2) (hh : wipn ≫ wtau = wtau2 ≫ wln)
    (hf : lh = c1 ≫ wuph ≫ lam) (hg : wipn ≫ lmh = lam ≫ ipn) (hl : lmh ≫ iv = 𝟙 A10)
    (hk : li ≫ lh = 𝟙 A1) :
    (li ≫ wt ≫ mm) ≫ ikn = ipn ≫ iv ≫ wtau ≫ mu := by
  have key : li ≫ c1 ≫ wuph ≫ wipn = ipn ≫ iv := by
    rw [peelWhisker lam ipn iv lmh wipn hg hl, reassoc_of% (peelUnitor li lh c1 wuph lam hf hk)]
  simp only [Category.assoc]
  rw [hb, reassoc_of% hc, hd, Category.assoc, reassoc_of% hei, ← reassoc_of% hh, reassoc_of% key]

/-! ### The two cotensorators agree -/

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- The cotensorator of `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator` and the one of
`Stacks.AlgebraicGeometry.ProjChartIntPullbackMul` are the same morphism. -/
theorem pullbackCotensorator_eq_intCotensor (A B : Y.Modules) :
    pullbackCotensorator j A B = intCotensor j A B :=
  (pullbackCotensorator_eq j A B).trans
    (rebuild
      (congrArg (Scheme.Modules.pullback j).map
        (congrArg Iso.hom (tensorIsoTensorModules_eq Y A B)))
      (congrArg Iso.inv (tensorIsoTensorModules_eq Y'
        ((Scheme.Modules.pullback j).obj A) ((Scheme.Modules.pullback j).obj B))))

variable (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- **The canonical comparison family of the integer tensor powers under pullback.** -/
def intCompare : IntCompare j L := fun d => (intPullIso j L d).hom

/-- **The canonical comparison intertwines the two multiplications by `t`**, in every pair of
integer degrees and with no hypothesis. -/
theorem intCompare_intMulMap {k : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) (n : ℤ) :
    (Scheme.Modules.pullback j).map (intMulMap L (intSecOf L t) n) ≫ intCompare j L (k + n)
      = intCompare j L n ≫ intMulMap ((Scheme.Modules.pullback j).obj L)
          (intSecOf ((Scheme.Modules.pullback j).obj L)
            (intPullSection j L (intCompare j L) k t)) n := by
  have hsplit : (Scheme.Modules.pullback j).map (intMulMap L (intSecOf L t) n)
      = (Scheme.Modules.pullback j).map (λ_ (tensorPowerModule Y L n)).inv ≫
        (Scheme.Modules.pullback j).map
          (intSecOf L t ▷ tensorPowerModule Y L n) ≫
        (Scheme.Modules.pullback j).map (intMulIso L k n).hom :=
    ((Scheme.Modules.pullback j).map_comp _ _).trans
      (congrArg (fun z => (Scheme.Modules.pullback j).map
          (λ_ (tensorPowerModule Y L n)).inv ≫ z)
        ((Scheme.Modules.pullback j).map_comp _ _))
  have hb : (Scheme.Modules.pullback j).map (intMulIso L k n).hom ≫ intCompare j L (k + n)
      = pullbackCotensorator j (tensorPowerModule Y L k) (tensorPowerModule Y L n) ≫
        (intCompare j L k ⊗ₘ intCompare j L n) ≫
        (intMulIso ((Scheme.Modules.pullback j).obj L) k n).hom :=
    (intPullIso_intMulIso j L k n).trans
      (rebuild (pullbackCotensorator_eq_intCotensor j
        (tensorPowerModule Y L k) (tensorPowerModule Y L n)).symm rfl)
  have hc := pullbackCotensorator_whiskerRight j (intSecOf L t) (tensorPowerModule Y L n)
  have hd := MonoidalCategory.tensorHom_def (intCompare j L k) (intCompare j L n)
  have hsec : unitPullbackHom j ≫ intSecOf ((Scheme.Modules.pullback j).obj L)
        (intPullSection j L (intCompare j L) k t)
      = (Scheme.Modules.pullback j).map (intSecOf L t) ≫ intCompare j L k :=
    (congrArg (fun z => unitPullbackHom j ≫ z)
      (intSecOf_intPullSection j L (intCompare j L) k t)).trans
      (cancelFront (unitPullbackIso j).hom_inv_id _)
  have hei : ((Scheme.Modules.pullback j).map (intSecOf L t) ▷
          (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n)) ≫
        (intCompare j L k ▷ (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n))
      = (unitPullbackHom j ▷
          (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n)) ≫
        (intSecOf ((Scheme.Modules.pullback j).obj L)
            (intPullSection j L (intCompare j L) k t) ▷
          (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n)) :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
      ((congrArg (fun z => z ▷ (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n))
          hsec).symm.trans
        (MonoidalCategory.comp_whiskerRight _ _ _))
  have hh := MonoidalCategory.whisker_exchange
    (intSecOf ((Scheme.Modules.pullback j).obj L)
      (intPullSection j L (intCompare j L) k t)) (intCompare j L n)
  have hf := pullbackCotensorator_leftUnitor Y j (tensorPowerModule Y L n)
  have hg := MonoidalCategory.leftUnitor_naturality (intCompare j L n)
  have hl := (λ_ (tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) n)).hom_inv_id
  have hk := ((Scheme.Modules.pullback j).mapIso (λ_ (tensorPowerModule Y L n))).inv_hom_id
  exact (congrArg (fun z => z ≫ intCompare j L (k + n)) hsplit).trans
    (bigAssemble hb hc hd hei hh hf hg hl hk)

/-! ### The two consequences, with `hmul` discharged -/

/-- **The canonical comparison intertwines multiplication by `t` with multiplication by `j^*t` on
the sections over `V'`**, unconditionally. This is
`Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.intPullSectionOn_app_intMulMap` with its
hypothesis supplied by `intCompare_intMulMap`. -/
theorem intPullSectionOn_app_intMulMap {k : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) (n : ℤ)
    {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V) (a : Γ(tensorPowerModule Y L n, V)) :
    (intMulMap ((Scheme.Modules.pullback j).obj L)
          (intSecOf ((Scheme.Modules.pullback j).obj L)
            (intPullSection j L (intCompare j L) k t)) n).app V'
        (intPullSectionOn j L (intCompare j L) n hVV' a)
      = intPullSectionOn j L (intCompare j L) (k + n) hVV'
          ((intMulMap L (intSecOf L t) n).app V a) :=
  Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.intPullSectionOn_app_intMulMap
    j L (intCompare j L) t n (intCompare_intMulMap j L t n) hVV' a

/-- **Division across integer degrees commutes with pullback**, unconditionally: the hypothesis
of `Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.intDivTop_intPullSection` is
`intCompare_intMulMap`. -/
theorem intDivTop_intPullSection {k : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) (n : ℤ)
    {V : Y.Opens} (hV : V ≤ nonvanishingOpen Y (tensorPowerModule Y L k) t)
    (x : Γ(tensorPowerModule Y L (k + n), ⊤)) {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (hV' : V' ≤ nonvanishingOpen Y'
      (tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) k)
      (intPullSection j L (intCompare j L) k t)) :
    intDivTop ((Scheme.Modules.pullback j).obj L)
        (intPullSection j L (intCompare j L) k t) hV' n
        (intPullSection j L (intCompare j L) (k + n) x)
      = intPullSectionOn j L (intCompare j L) n hVV' (intDivTop L t hV n x) :=
  Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback.intDivTop_intPullSection
    j L (intCompare j L) t n (intCompare_intMulMap j L t n) hV x hVV' hV'

end Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback

end
