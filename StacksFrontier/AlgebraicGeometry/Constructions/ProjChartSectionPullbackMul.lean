module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection

/-!
# Pulling back a product of global sections of tensor powers

Let `j : Y' ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module.
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` carries a global section of
`L ^⊗ n` to a global section of `(j^*L) ^⊗ n`, through the comparison
`pullbackNatTensorPowIso`, and
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` is the product of two global sections
of tensor powers. This file reduces the **multiplicativity**

  `pullSection j L (n + m) (s · t) = pullSection j L n s · pullSection j L m t`

to a single identity between morphisms of `𝒪_{Y'}`-modules, proves that identity in degree
`m = 0`, and proves it in every degree from the successor recursion of the comparison.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullbackNatTensorPowIso_inv`: the inverse of
  the comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` **is** the comparison
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` of the integer tensor powers; the two
  families of powers agree in nonnegative degree and the transports between them are identities.
* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullbackNatTensorPowIso_inv_zero`: in degree
  zero that comparison is the structure-sheaf comparison
  `Stacks.PullbackUnitSection.unitPullbackHom`.
* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.secOf_pullSection`: **the pulled-back section,
  read as a morphism out of the monoidal unit**, is the image under `j^*` of the original such
  morphism, preceded by the structure-sheaf comparison and followed by the comparison of the
  powers.
* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_mulMap`:
  **the reduction.** Multiplicativity of `pullSection` in a fixed pair of degrees follows from the
  single identity
  `j^*(mulMap σ m) ≫ c (n + m) = c m ≫ mulMap σ' m`,
  where `σ` is the first factor read as a morphism out of the unit, `σ'` is its pullback, and `c`
  is the comparison of the powers.
* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_zero`:
  **multiplicativity when the second factor has degree zero**, unconditionally.
* `Stacks.AlgebraicGeometry.ProjChartSectionPullback.mulMap_comp_pullbackNatTensorPowIso_inv` and
  `pullSection_mulSections_of_succ`: that identity, and hence multiplicativity in every pair of
  degrees, from a cotensorator for `j^*` in the first variable which computes the successor step
  of the comparison.

## Implementation notes

**Why the reduction is where the statement about sections stops.** A global section of `L ^⊗ k` is
a morphism `𝟙_ ⟶ L ^⊗ k` out of the monoidal unit
(`Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf`), the product of two of them is the second
followed by `Stacks.GradedSections.mulMap` of the first
(`Stacks.SectionProduct.globalSection_mul`), and pulling a global section back is `j^*` applied to
that morphism, read through the structure-sheaf comparison
(`Stacks.PullbackUnitSection.pullbackSectionHom_globalSection`). So every section in the statement
disappears, and what is left is one equation between morphisms. Nothing about sections is needed
after that point, and in particular no local description of a section of a tensor product is used.

**Why the degree-zero case is unconditional.** `mulMap σ 0` is `σ` itself, and the comparison in
degree zero is the structure-sheaf comparison, which is inverse to the morphism through which
`j^*` takes a morphism out of the unit again to a morphism out of the unit. So the identity in
degree zero is the cancellation of that isomorphism against its inverse.

**The transparency discipline.** A goal mentioning both `AlgebraicGeometry.Scheme.Modules.pullback`
and `RingedSpaceModuleAdjunction.modulePullback`, or both `n + (m + 1)` and `n + m + 1` as the
exponent of a tensor power, is definitionally correct but not type-correct at the transparency the
rewriting tactics check their motives at. Three measures are used, each of them the one the
neighbouring files use: `attribute [local implicit_reducible]
Stacks.TensorPowers.natTensorPow`, so that the successor of a power is reducibly a tensor product;
`show` to normalise the exponent before rewriting; and, where a cancellation is needed in front of
a composite whose type crosses two spellings of the module pullback, the helper `cancel_front`,
stated with its objects as variables so that the crossing happens once inside a defeq-tolerant
`exact`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)

## Where the hypotheses are discharged

The family `δ` that
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_succ` asks for is
a cotensorator for `j^*` **at the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory`**, in which `Stacks.TensorPowers.natTensorPow`
and `Stacks.GradedSections.mulMap` are read, computing the successor step of
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. It is built in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjChartPullbackCotensorator.lean` as
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator`, from the comparison
of Stacks Tag 01CD conjugated by `Stacks.AmplePullbackPart1.tensorIsoTensorModules` on each side;
the naturality of that conjugation is
`Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality`, and the successor step is the
normalisation `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_one_right_natCast` of the
multiplication of the powers in bidegree `(k, 1)`. The conclusion with no hypothesis is
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (mul mulMap mul_def mulMap_zero mulMap_succ)
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf mulSections globalSection_secOf
  secOf_globalSection mulSections_globalSection)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.PullbackUnitSection (unitPullback unitPullbackHom unitPullbackIso
  pullbackSectionHom_globalSection)
open Stacks.RelativeVeryAmple (pullbackTensorPowModuleIso)

universe v u w

namespace Stacks.AlgebraicGeometry.ProjChartSectionPullback

/-- A morphism split off the front of a composite, when a retraction of it is available, with the
objects as variables. The crossing between two spellings of the module pullback happens once, in
the application of this lemma, rather than inside a rewrite whose motive is checked at a lower
transparency. -/
private theorem cancel_front {E : Type w} [Category.{v} E] {A B C D : E} (p : A ⟶ B) (q : B ⟶ A)
    (hpq : p ≫ q = 𝟙 A) (g : A ⟶ C) (h : C ⟶ D) : p ≫ (q ≫ g) ≫ h = g ≫ h := by
  rw [Category.assoc, ← Category.assoc p, hpq, Category.id_comp]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y L]

/-! ### The comparison of the powers, identified -/

/-- **The comparison of the left-iterated powers is the comparison of the integer powers.** The
two readings of the tensor powers agree in nonnegative degree and the transports
`Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule` between them are identities, so the
inverse of `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` is
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` outright. -/
theorem pullbackNatTensorPowIso_inv (n : ℕ) :
    (pullbackNatTensorPowIso j L n).inv = (pullbackTensorPowModuleIso j L n).hom :=
  Eq.trans (Category.comp_id _)
    (Eq.trans (congrArg (fun z => z ≫ (pullbackTensorPowModuleIso j L n).hom)
        ((Scheme.Modules.pullback j).map_id (natTensorPow L n)))
      (Category.id_comp _))

/-- **In degree zero the comparison of the powers is the structure-sheaf comparison.** The zeroth
power is the monoidal unit, the identification of the zeroth power with the free rank-one sheaf is
the counit of sheafification on both sides, and the comparison of the pullbacks of those sheaves
is the one `Stacks.PullbackUnitSection.unitPullbackHom` is built from. -/
theorem pullbackNatTensorPowIso_inv_zero :
    (pullbackNatTensorPowIso j L 0).inv = unitPullbackHom j :=
  pullbackNatTensorPowIso_inv j L 0

/-! ### The pulled-back section as a morphism out of the unit -/

/-- **The pullback of a global section of `L ^⊗ n`, read as a morphism out of the monoidal
unit.** It is the image under `j^*` of the original morphism out of the unit, preceded by the
morphism `Stacks.PullbackUnitSection.unitPullback` through which `j^*` takes a morphism out of the
unit again to a morphism out of the unit, and followed by the comparison of the powers. -/
theorem secOf_pullSection (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n x)
      = unitPullback j ≫ (Scheme.Modules.pullback j).map (secOf L x) ≫
          (pullbackNatTensorPowIso j L n).inv := by
  refine (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y'
    (natTensorPow ((Scheme.Modules.pullback j).obj L) n)).symm_apply_eq.mpr ?_
  change pullSection j L n x = globalSection Y' _ _
  rw [← Category.assoc, Stacks.SectionProduct.globalSection_comp _ _ (unitPullback j ≫
      (Scheme.Modules.pullback j).map (secOf L x)) (pullbackNatTensorPowIso j L n).inv,
    ← pullbackSectionHom_globalSection j (natTensorPow L n) (secOf L x), globalSection_secOf]
  rfl

/-! ### The reduction to one identity of morphisms -/

/-- A product of global sections of tensor powers is the global section of the product of the
morphisms out of the unit that they define. -/
private theorem mulSections_eq_globalSection_mul {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {n m : ℕ} (s : Γ(natTensorPow M n, ⊤))
    (t : Γ(natTensorPow M m, ⊤)) :
    mulSections M s t = globalSection X _ (mul (secOf M s) (secOf M t)) := by
  rw [← mulSections_globalSection, globalSection_secOf, globalSection_secOf]

/-- **Multiplicativity of the pullback of sections, reduced to one identity of morphisms.**
Writing `σ` for the first factor read as a morphism out of the monoidal unit, `σ'` for the
pullback of that factor read the same way, and `c k` for the comparison
`j^*(L ^⊗ k) ⟶ (j^*L) ^⊗ k`, the hypothesis is the single square

  `j^*(mulMap σ m) ≫ c (n + m) = c m ≫ mulMap σ' m`,

and the conclusion is that pulling back the product of two global sections of tensor powers is the
product of their pullbacks.

Both sides are global sections of the same module, so both are read as morphisms out of the
monoidal unit: on the left by `secOf_pullSection` and the description of a product of sections as
multiplication by the first factor, on the right by `secOf_pullSection` applied to each factor. -/
theorem pullSection_mulSections_of_mulMap {n m : ℕ} (s : Γ(natTensorPow L n, ⊤))
    (t : Γ(natTensorPow L m, ⊤))
    (hmul : (Scheme.Modules.pullback j).map (mulMap (secOf L s) m) ≫
          (pullbackNatTensorPowIso j L (n + m)).inv
        = (pullbackNatTensorPowIso j L m).inv ≫
          mulMap (secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)) m) :
    pullSection j L (n + m) (mulSections L s t)
      = mulSections ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)
          (pullSection j L m t) := by
  have h2 : secOf L (mulSections L s t) = mul (secOf L s) (secOf L t) := by
    rw [mulSections_eq_globalSection_mul, secOf_globalSection]
  have hL : pullSection j L (n + m) (mulSections L s t)
      = globalSection Y' _ (secOf ((Scheme.Modules.pullback j).obj L)
          (pullSection j L (n + m) (mulSections L s t))) :=
    (globalSection_secOf _ _).symm
  rw [hL, mulSections_eq_globalSection_mul ((Scheme.Modules.pullback j).obj L),
    secOf_pullSection j L (n + m) (mulSections L s t), h2,
    secOf_pullSection j L m t, mul_def, mul_def, (Scheme.Modules.pullback j).map_comp]
  simp only [Category.assoc]
  rw [hmul]

/-! ### Degree zero in the second factor -/

/-- **The identity of morphisms in degree zero.** `mulMap σ 0` is `σ`, the comparison in degree
zero is the structure-sheaf comparison, and that comparison cancels against the morphism
`Stacks.PullbackUnitSection.unitPullback` through which the pulled-back section is read. -/
theorem mulMap_comp_pullbackNatTensorPowIso_inv_zero {n : ℕ} (s : Γ(natTensorPow L n, ⊤)) :
    (Scheme.Modules.pullback j).map (mulMap (secOf L s) 0) ≫
        (pullbackNatTensorPowIso j L (n + 0)).inv
      = (pullbackNatTensorPowIso j L 0).inv ≫
        mulMap (secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)) 0 := by
  rw [mulMap_zero, mulMap_zero, secOf_pullSection, pullbackNatTensorPowIso_inv_zero]
  exact (cancel_front (unitPullbackHom j) (unitPullback j)
    (unitPullbackIso j).hom_inv_id _ _).symm

/-- **Pulling back a product is the product of the pullbacks, when the second factor has degree
zero.** This is the case of multiplicativity that the structure-sheaf comparison of Stacks Tag
01CD settles on its own. -/
theorem pullSection_mulSections_zero {n : ℕ} (s : Γ(natTensorPow L n, ⊤))
    (t : Γ(natTensorPow L 0, ⊤)) :
    pullSection j L (n + 0) (mulSections L s t)
      = mulSections ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)
          (pullSection j L 0 t) :=
  pullSection_mulSections_of_mulMap j L s t
    (mulMap_comp_pullbackNatTensorPowIso_inv_zero j L s)

/-! ### Every degree, from the successor recursion of the comparison -/

/-- **The identity of morphisms in every degree**, from a cotensorator for `j^*` in the first
variable which computes the successor step of the comparison of the powers. The induction is on
the second exponent: the base case is
`mulMap_comp_pullbackNatTensorPowIso_inv_zero`, and the step is the naturality of the cotensorator
applied to `mulMap σ m`, followed by the inductive hypothesis whiskered by `j^*L`. -/
theorem mulMap_comp_pullbackNatTensorPowIso_inv
    (δ : (A : Y.Modules) → (Scheme.Modules.pullback j).obj (A ⊗ L) ⟶
      (Scheme.Modules.pullback j).obj A ⊗ (Scheme.Modules.pullback j).obj L)
    (hδ : ∀ {A A' : Y.Modules} (h : A ⟶ A'),
      (Scheme.Modules.pullback j).map (h ▷ L) ≫ δ A'
        = δ A ≫ ((Scheme.Modules.pullback j).map h ▷ (Scheme.Modules.pullback j).obj L))
    (hsucc : ∀ k : ℕ, (pullbackNatTensorPowIso j L (k + 1)).inv
      = δ (natTensorPow L k) ≫ ((pullbackNatTensorPowIso j L k).inv ▷
          (Scheme.Modules.pullback j).obj L))
    {n : ℕ} (s : Γ(natTensorPow L n, ⊤)) : ∀ m : ℕ,
    (Scheme.Modules.pullback j).map (mulMap (secOf L s) m) ≫
        (pullbackNatTensorPowIso j L (n + m)).inv
      = (pullbackNatTensorPowIso j L m).inv ≫
        mulMap (secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)) m
  | 0 => mulMap_comp_pullbackNatTensorPowIso_inv_zero j L s
  | m + 1 => by
      have ih := mulMap_comp_pullbackNatTensorPowIso_inv δ hδ hsucc s m
      change _ ≫ (pullbackNatTensorPowIso j L (n + m + 1)).inv = _
      rw [mulMap_succ, mulMap_succ, hsucc (n + m), hsucc m, ← Category.assoc,
        hδ (mulMap (secOf L s) m), Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        ih, MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- **Pulling back a product of global sections of tensor powers is the product of the
pullbacks**, from a cotensorator for `j^*` in the first variable which computes the successor step
of the comparison of the powers. This is what makes the pullback of a datum of graded sections a
datum of graded sections again, its multiplicativity clause being exactly this identity. -/
theorem pullSection_mulSections_of_succ
    (δ : (A : Y.Modules) → (Scheme.Modules.pullback j).obj (A ⊗ L) ⟶
      (Scheme.Modules.pullback j).obj A ⊗ (Scheme.Modules.pullback j).obj L)
    (hδ : ∀ {A A' : Y.Modules} (h : A ⟶ A'),
      (Scheme.Modules.pullback j).map (h ▷ L) ≫ δ A'
        = δ A ≫ ((Scheme.Modules.pullback j).map h ▷ (Scheme.Modules.pullback j).obj L))
    (hsucc : ∀ k : ℕ, (pullbackNatTensorPowIso j L (k + 1)).inv
      = δ (natTensorPow L k) ≫ ((pullbackNatTensorPowIso j L k).inv ▷
          (Scheme.Modules.pullback j).obj L))
    {n m : ℕ} (s : Γ(natTensorPow L n, ⊤)) (t : Γ(natTensorPow L m, ⊤)) :
    pullSection j L (n + m) (mulSections L s t)
      = mulSections ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)
          (pullSection j L m t) :=
  pullSection_mulSections_of_mulMap j L s t
    (mulMap_comp_pullbackNatTensorPowIso_inv j L δ hδ hsucc s m)

end Stacks.AlgebraicGeometry.ProjChartSectionPullback

end
