module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.VeroneseChartBidegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Situation 01QH's map is a map of `ℤ`-graded `𝒪_X`-algebras

Let `X` be a scheme, `𝓛` an ample invertible sheaf on `X`, `S = Γ_*(X, 𝓛)` and `Y = Proj S`, and
let `f : X ⟶ Y` be the canonical morphism of [Stacks, Tag 01PZ].  Situation [Stacks, Tag 01QH]
equips `f` with a `ℤ`-graded `𝒪_X`-algebra map `⨁_{n ∈ ℤ} f^*𝒪_Y(n) ⟶ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`.  Its
degreewise components are `Stacks.SectionRingVeroneseChart.twistComparison`; **this file supplies
the multiplicativity, in an arbitrary integer bidegree, which is what makes the family a map of
graded algebras rather than a family of maps.**

`twistComparison` is the forward map of a composite of five isomorphisms and the bidegree square
for it is the five legs' squares pasted.  Four of the five are proved elsewhere:

* the twist leg on [Stacks, Tag 01MU]'s open `W₁`, pulled back along the lift —
  `Stacks.SectionRingVeroneseChart.pullbackTheta_mul`, which rests on
  `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul`;
* the pullback leg —
  `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackTensorPowModuleIntIso_mul`;
* the transport leg, which occurs twice —
  `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_mul`.

What is added here is the square for the remaining structural leg
`Stacks.SectionRingVeroneseChart.pbTwistIsoGood` and the pasting of the five.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistTensor.twistMulModules`: **the canonical multiplication
  `𝒪_Y(n) ⊗ 𝒪_Y(m) ⟶ 𝒪_Y(n + m)` of [Stacks, Tag 01MO], ascribed at the
  `Stacks.RelativeVeryAmple.tensorModules` spelling** of the tensor product of the sheaves of
  modules of the scheme `Proj 𝒮`.  See the implementation notes for why the ascription is needed
  and why it is at that spelling and not at `⊗`.
* `Stacks.SectionRingVeroneseChart.pbTwistMul`: **the graded `𝒪_X`-algebra structure on
  `⨁_{n ∈ ℤ} f^*𝒪_Y(n)`** — `twistMulModules` pulled back along `f` and conjugated by
  [Stacks, Tag 01CD].  This is the source algebra of Situation [Stacks, Tag 01QH]'s map.

## Main results

* `Stacks.SectionRingVeroneseChart.twistComparison_mul`: **multiplicativity of Situation
  [Stacks, Tag 01QH]'s map in an arbitrary integer bidegree `(n, m)`** — `pbTwistMul` followed by
  the comparison in the degree `n + m` is the comparisons in the degrees `n` and `m` on the two
  factors followed by the addition law `Stacks.Ample.tensorPowModuleAddIso` of
  [Stacks, Tag 01CU] for the tensor powers of `𝓛`.
* `Stacks.SectionRingVeroneseChart.pbTwistIsoGood_mul`: **the remaining structural leg's square.**
* `Stacks.Monoidal.pullbackComp_mul_eqToHom`: the transport along an equality of morphisms and the
  composition law for pullback, pasted, for an arbitrary multiplication on the base.
* `Stacks.Monoidal.paste5_free`, `square_of_eq_free`, `square_transfer_free`: the free-shape steps
  the pasting of a five-leg composite is assembled from.

## Implementation notes

**The ascription, and why it is at `tensorModules` and not at `⊗`.**  The monoidal structure of
[Stacks, Tag 01CA] is not registered at the `SheafOfModules (projStructureRing 𝒮)` spelling that
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` carries — which is why
`Stacks.AlgebraicGeometry.TwistTensor.twistMul` already exists as a retyping at the
tensor-bifunctor spelling — while every statement about the comparison of [Stacks, Tag 01CD] for a
morphism of *schemes* is read at `Stacks.RelativeVeryAmple.tensorModules`.  Writing the source as
`(twistingSheaf 𝒮 n : (AlgebraicGeometry.Proj 𝒮).Modules) ⊗ _` does not work: the ascription
leaves the type at the `projStructureRing` spelling and instance search then fails outright for
`MonoidalCategoryStruct` there.  At `tensorModules` it succeeds, and that is the
spelling `twistMulModules` is given.

**Every defeq step is isolated into its own `rfl` lemma.**  This is the discipline the two
obstacles described in
`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartBidegree.lean` force, and it is what
makes the chase fit in the heartbeat allowance:

* `pbTwistMul_eq`, `goodTwistMul_eq` and `pbTwistIsoGood_hom` unfold the two multiplications and
  the leg, each on its own;
* `Stacks.Monoidal.square_transfer_free` and `square_of_eq_free` move a square from one spelling of
  its edges and multiplications to another, taking those unfoldings as inputs, so no two of them
  are ever demanded in a single unification.

Pasting the two halves of the first structural leg's square directly at the concrete objects —
`Stacks.Monoidal.paste_squares_free` applied to the transport and the composition law, with the
`eqToHom`s and the components of `AlgebraicGeometry.Scheme.Modules.pullbackComp` written out —
exceeds the heartbeat allowance in `isDefEq` whether the arguments are left to unification or
supplied explicitly; so does composing the two in a single `exact` against the compact statement
(`whnf`).  Both fail at 200 000 heartbeats.  `pullbackComp_mul_eqToHom` performs that
paste with the schemes, the morphisms and the modules all variables, where `cases` on the equality
of morphisms collapses the transports to identities, and the concrete leg is a single
instantiation of it.

**The five-leg pasting names everything.**  `paste5_free` takes each of the six multiplications
and each of the fifteen edges as an explicit argument, so the unifier never has to hold two legs'
terms at once; `twistComparison_eq` then reads the pasted square at `twistComparison`.

**Every proof is term-level.**  The goals mention both spellings of the structure-ring sheaf of a
scheme, so they are not type-correct at `implicit` transparency and neither `rw` nor `simp only`
fires on them; the tactic proofs below are all inside free-shape lemmas, where every object and
morphism is a variable.

**Where unit preservation is.**  A `Stacks.SheafOfModules.GradedAlgebra.Hom` — this
repository's notion of a homomorphism of sheaves of `ℤ`-graded algebras, registered for
[Stacks, Tag 0FQW] — is exactly a degreewise family together with multiplicativity in every
bidegree, and that is what `twistComparison` and `twistComparison_mul` supply between them.  Unit
preservation, the extra datum of `Stacks.SheafOfModules.GradedAlgebra.UnitalHom`, is
`Stacks.SectionRingVeroneseChart.pbTwistUnit_twistComparison` of
`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebraUnit.lean`; the three
declarations jointly give the Situation's `ℤ`-graded `𝒪_X`-algebra map.

It is proved there from the bidegree square below rather than independently of it: the degree-zero
pieces of both algebras are `𝒪_X`, both units are forced, and the square at a bidegree `(0, m)`
makes the two candidates agree after tensoring on the right by `f^*𝒪_Y(m)` — which is invertible,
so tensoring by it is faithful ([Stacks, Tag 0FFM]) and the factor comes off.  No argument about
global sections enters: the uniqueness of a unit for an invertible-object multiplication is a
cancellation, not a computation.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.GoodOpenIntTwist (goodOpen twist theta)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.AlgebraicGeometry.PullbackTensorPowInt
open Stacks.AlgebraicGeometry.TensorPowCongrInt (tensorPowModuleIsoOfIsoInt_mul)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)

namespace Stacks.Monoidal

section Free

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **A bidegree square with its three vertical edges replaced by equal morphisms.**  This is how
a square proved at one spelling of its edges is read at another; the three equations are the
`rfl`s that unfold the edges. -/
theorem square_of_eq_free {A B C A' B' C' : D} {u : A ⊗ B ⟶ C} {u' : A' ⊗ B' ⟶ C'}
    {a a₀ : A ⟶ A'} {b b₀ : B ⟶ B'} {c c₀ : C ⟶ C'}
    (ha : a = a₀) (hb : b = b₀) (hc : c = c₀)
    (h : u ≫ c₀ = (a₀ ⊗ₘ b₀) ≫ u') : u ≫ c = (a ⊗ₘ b) ≫ u' := by
  subst ha; subst hb; subst hc; exact h

/-- **A bidegree square with its three vertical edges and both multiplications replaced by equal
morphisms.**  The five equations are supplied as separate `rfl` lemmas, which is what keeps the
unfoldings out of a single unification. -/
theorem square_transfer_free {A B C A' B' C' : D} {u u₀ : A ⊗ B ⟶ C} {u' u₀' : A' ⊗ B' ⟶ C'}
    {a a₀ : A ⟶ A'} {b b₀ : B ⟶ B'} {c c₀ : C ⟶ C'}
    (hu : u = u₀) (hu' : u' = u₀') (ha : a = a₀) (hb : b = b₀) (hc : c = c₀)
    (h : u₀ ≫ c₀ = (a₀ ⊗ₘ b₀) ≫ u₀') : u ≫ c = (a ⊗ₘ b) ≫ u' := by
  subst hu hu'
  exact square_of_eq_free ha hb hc h

/-- **Five bidegree squares in a row paste to one.**  The vertical edges of the pasted square are
the five squares' composites, nested exactly as a fivefold `CategoryTheory.Iso.trans` of the shape
`(e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄) ≪≫ e₅` nests them — which is the shape of
`Stacks.SectionRingVeroneseChart.twistComparisonIso`.

Each of the six multiplications and each of the fifteen edges is a named argument, so that
instantiating this lemma never asks the unifier to hold two legs' terms at once. -/
theorem paste5_free {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ A₄ B₄ C₄ A₅ B₅ C₅ A₆ B₆ C₆ : D}
    (u₁ : A₁ ⊗ B₁ ⟶ C₁) (u₂ : A₂ ⊗ B₂ ⟶ C₂) (u₃ : A₃ ⊗ B₃ ⟶ C₃) (u₄ : A₄ ⊗ B₄ ⟶ C₄)
    (u₅ : A₅ ⊗ B₅ ⟶ C₅) (u₆ : A₆ ⊗ B₆ ⟶ C₆)
    (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂)
    (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃)
    (a₃ : A₃ ⟶ A₄) (b₃ : B₃ ⟶ B₄) (c₃ : C₃ ⟶ C₄)
    (a₄ : A₄ ⟶ A₅) (b₄ : B₄ ⟶ B₅) (c₄ : C₄ ⟶ C₅)
    (a₅ : A₅ ⟶ A₆) (b₅ : B₅ ⟶ B₆) (c₅ : C₅ ⟶ C₆)
    (h₁ : u₁ ≫ c₁ = (a₁ ⊗ₘ b₁) ≫ u₂) (h₂ : u₂ ≫ c₂ = (a₂ ⊗ₘ b₂) ≫ u₃)
    (h₃ : u₃ ≫ c₃ = (a₃ ⊗ₘ b₃) ≫ u₄) (h₄ : u₄ ≫ c₄ = (a₄ ⊗ₘ b₄) ≫ u₅)
    (h₅ : u₅ ≫ c₅ = (a₅ ⊗ₘ b₅) ≫ u₆) :
    u₁ ≫ (c₁ ≫ c₂ ≫ c₃ ≫ c₄) ≫ c₅ =
      ((a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ a₅ ⊗ₘ (b₁ ≫ b₂ ≫ b₃ ≫ b₄) ≫ b₅) ≫ u₆ := by
  have p₂ := paste_squares_free u₁ u₂ u₃ a₁ b₁ c₁ a₂ b₂ c₂ h₁ h₂
  have p₃ := paste_squares_free u₁ u₃ u₄ (a₁ ≫ a₂) (b₁ ≫ b₂) (c₁ ≫ c₂) a₃ b₃ c₃ p₂ h₃
  have p₄ := paste_squares_free u₁ u₄ u₅ ((a₁ ≫ a₂) ≫ a₃) ((b₁ ≫ b₂) ≫ b₃)
    ((c₁ ≫ c₂) ≫ c₃) a₄ b₄ c₄ p₃ h₄
  have p₅ := paste_squares_free u₁ u₅ u₆ (((a₁ ≫ a₂) ≫ a₃) ≫ a₄) (((b₁ ≫ b₂) ≫ b₃) ≫ b₄)
    (((c₁ ≫ c₂) ≫ c₃) ≫ c₄) a₅ b₅ c₅ p₄ h₅
  simpa only [Category.assoc] using p₅

end Free

/-! ### The transport along an equality of morphisms, pasted with the composition law -/

section Pullback

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

/-- **The transport along an equality of morphisms, followed by the composition law for pullback,
is multiplicative.**  A morphism `u : A ⊗ B ⟶ C` of `𝒪_S`-modules induces a multiplication of the
pullbacks along any morphism, by inverting the comparison of [Stacks, Tag 01CD] and applying the
pullback.  If `φ = p ≫ q`, then the transport along that equality followed by
`AlgebraicGeometry.Scheme.Modules.pullbackComp` carries the multiplication induced on the
pullbacks along `φ` to the one induced on the iterated pullbacks along `q` and then `p`.

This is `Stacks.Monoidal.pullback_mul_eqToHom` pasted with
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackComp_mul`.  The paste is done here, with the
schemes, the morphisms and the modules all variables, because at the concrete objects of
`Stacks.SectionRingVeroneseChart.pbTwistIsoGood_mul` it exceeds the heartbeat allowance; see the
implementation notes of this file. -/
theorem pullbackComp_mul_eqToHom {X W S : Scheme.{u}} (p : X ⟶ W) (q : W ⟶ S) {φ : X ⟶ S}
    (e : φ = p ≫ q) {A B C : S.Modules} (u : A ⊗ B ⟶ C) :
    ((pullbackTensorModulesIso φ A B).inv ≫ (Scheme.Modules.pullback φ).map u) ≫
        (eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj C) e) ≫
          ((Scheme.Modules.pullbackComp p q).app C).inv) =
      ((eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj A) e) ≫
            ((Scheme.Modules.pullbackComp p q).app A).inv) ⊗ₘ
          (eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj B) e) ≫
            ((Scheme.Modules.pullbackComp p q).app B).inv)) ≫
        ((pullbackTensorModulesIso p ((Scheme.Modules.pullback q).obj A)
            ((Scheme.Modules.pullback q).obj B)).inv ≫
          (Scheme.Modules.pullback p).map
            ((pullbackTensorModulesIso q A B).inv ≫ (Scheme.Modules.pullback q).map u)) := by
  cases e
  simp only [eqToHom_refl, Category.id_comp]
  exact (Category.assoc _ _ _).trans
    (Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackComp_mul p q u)

end Pullback

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.TwistTensor

/-! ### The multiplication of the twisting sheaves, at the modules of the scheme `Proj 𝒮` -/

section Ascription

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The canonical multiplication `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` of [Stacks, Tag 01MO], ascribed at
the `Stacks.RelativeVeryAmple.tensorModules` spelling** of the tensor product of the sheaves of
modules of the scheme `Proj 𝒮`.  That is the spelling every statement about the comparison of
[Stacks, Tag 01CD] for a morphism of schemes is read at, so it is the spelling the multiplication
has to be given at before it can be pulled back.  The body is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`; the ascription is the whole
content, and `twistMulModules_eq` records that it changes no term.

This is the fourth ascription of this one map: `twistMultiplicationMap` is stated at
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`,
`Stacks.AlgebraicGeometry.TwistTensor.twistMul` retypes it at the tensor-bifunctor spelling of
`SheafOfModules (projStructureRing 𝒮)` and `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulIso`
packages it as an isomorphism once the degree-one elements cover. -/
@[ega "II 8.1.5" "special case", ega "II 8.14.2" "special case"]
def twistMulModules (n m : ℤ) :
    tensorModules (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 n) (twistingSheaf 𝒮 m) ⟶
      twistingSheaf 𝒮 (n + m) :=
  twistMultiplicationMap 𝒮 n m

/-- **The retyping changes no term.** -/
theorem twistMulModules_eq (n m : ℤ) :
    twistMulModules 𝒮 n m = twistMultiplicationMap 𝒮 n m :=
  rfl

end Ascription

end Stacks.AlgebraicGeometry.TwistTensor

namespace Stacks.SectionRingVeroneseChart

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

/-! ### The graded algebra structure on `⨁_{n ∈ ℤ} f^*𝒪_Y(n)` -/

/-- **The graded `𝒪_X`-algebra structure on `⨁_{n ∈ ℤ} f^*𝒪_Y(n)`**: the canonical multiplication
`Stacks.AlgebraicGeometry.TwistTensor.twistMulModules` of the twisting sheaves of
[Stacks, Tag 01MO], pulled back along the canonical morphism of [Stacks, Tag 01PZ] and conjugated
by the comparison of [Stacks, Tag 01CD].  This is the source algebra of Situation
[Stacks, Tag 01QH]'s map. -/
def pbTwistMul (n m : ℤ) :
    pbTwist L hL n ⊗ pbTwist L hL m ⟶ pbTwist L hL (n + m) :=
  (pullbackTensorModulesIso (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)
      (twistingSheaf (grading L) n) (twistingSheaf (grading L) m)).inv ≫
    (Scheme.Modules.pullback (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)).map
      (Stacks.AlgebraicGeometry.TwistTensor.twistMulModules (grading L) n m)

/-- The source multiplication, unfolded. -/
theorem pbTwistMul_eq (n m : ℤ) :
    pbTwistMul L hL n m =
      (pullbackTensorModulesIso (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)
          (twistingSheaf (grading L) n) (twistingSheaf (grading L) m)).inv ≫
        (Scheme.Modules.pullback (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)).map
          (Stacks.AlgebraicGeometry.TwistTensor.twistMulModules (grading L) n m) :=
  rfl

/-- **The multiplication isomorphism of the twists on `W₁`, unfolded.**
`Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso` is [Stacks, Tag 01CD] inverted followed by
the restriction of the multiplication map of [Stacks, Tag 01MO]; this names that composite, so that
`goodTwistMul_eq` below is a congruence under one pullback rather than one defeq of the whole
composite. -/
private theorem twistMulIso_hom_unfold (n m : ℤ) :
    (Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso (grading L) n m).hom =
      (pullbackTensorModulesIso (goodOpen (grading L)).ι (twistingSheaf (grading L) n)
          (twistingSheaf (grading L) m)).inv ≫
        (Scheme.Modules.pullback (goodOpen (grading L)).ι).map
          (Stacks.AlgebraicGeometry.TwistTensor.twistMulModules (grading L) n m) :=
  rfl

/-- The multiplication of the pullbacks along the lift through `W₁`, unfolded as the
multiplication induced on an iterated pullback.  `Stacks.SectionRingVeroneseChart.goodTwistMul` is
defined through `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso`, which is itself the
restricted multiplication conjugated by [Stacks, Tag 01CD]; this is that composite written out. -/
theorem goodTwistMul_eq (n m : ℤ) :
    goodTwistMul L hL n m =
      (pullbackTensorModulesIso (goodLift L hL)
          ((Scheme.Modules.pullback (goodOpen (grading L)).ι).obj
            (twistingSheaf (grading L) n))
          ((Scheme.Modules.pullback (goodOpen (grading L)).ι).obj
            (twistingSheaf (grading L) m))).inv ≫
        (Scheme.Modules.pullback (goodLift L hL)).map
          ((pullbackTensorModulesIso (goodOpen (grading L)).ι (twistingSheaf (grading L) n)
              (twistingSheaf (grading L) m)).inv ≫
            (Scheme.Modules.pullback (goodOpen (grading L)).ι).map
              (Stacks.AlgebraicGeometry.TwistTensor.twistMulModules (grading L) n m)) :=
  congrArg (fun z ↦ (pullbackTensorModulesIso (goodLift L hL)
      ((Scheme.Modules.pullback (goodOpen (grading L)).ι).obj (twistingSheaf (grading L) n))
      ((Scheme.Modules.pullback (goodOpen (grading L)).ι).obj
        (twistingSheaf (grading L) m))).inv ≫
    (Scheme.Modules.pullback (goodLift L hL)).map z) (twistMulIso_hom_unfold L n m)

/-- The forward map of the first structural leg, unfolded: a transport along
`Stacks.SectionRingVeroneseChart.goodLift_comp_ι` followed by the composition law for pullback. -/
theorem pbTwistIsoGood_hom (c : ℤ) :
    (pbTwistIsoGood L hL c).hom =
      eqToHom (congrArg (fun χ : X ⟶ AlgebraicGeometry.Proj (grading L) ↦
          (Scheme.Modules.pullback χ).obj (twistingSheaf (grading L) c))
        (goodLift_comp_ι L hL).symm) ≫
        ((Scheme.Modules.pullbackComp (goodLift L hL) (goodOpen (grading L)).ι).app
          (twistingSheaf (grading L) c)).inv :=
  rfl

/-! ### The remaining structural leg -/

/-- **The first structural leg's square**: `pbTwistIsoGood` carries the multiplication
`pbTwistMul` of the pullbacks along the canonical morphism to the multiplication `goodTwistMul` of
the pullbacks along the lift through [Stacks, Tag 01MU]'s open `W₁`.

This is `Stacks.Monoidal.pullbackComp_mul_eqToHom` at `p = goodLift`, `q = (W₁ ⟶ Proj 𝒮)`, the
equality `Stacks.SectionRingVeroneseChart.goodLift_comp_ι` and the ascribed multiplication of the
twisting sheaves, read at the three unfoldings above. -/
theorem pbTwistIsoGood_mul (n m : ℤ) :
    pbTwistMul L hL n m ≫ (pbTwistIsoGood L hL (n + m)).hom =
      ((pbTwistIsoGood L hL n).hom ⊗ₘ (pbTwistIsoGood L hL m).hom) ≫
        goodTwistMul L hL n m :=
  Stacks.Monoidal.square_transfer_free (pbTwistMul_eq L hL n m) (goodTwistMul_eq L hL n m)
    (pbTwistIsoGood_hom L hL n) (pbTwistIsoGood_hom L hL m) (pbTwistIsoGood_hom L hL (n + m))
    (Stacks.Monoidal.pullbackComp_mul_eqToHom (goodLift L hL) (goodOpen (grading L)).ι
      (goodLift_comp_ι L hL).symm
      (Stacks.AlgebraicGeometry.TwistTensor.twistMulModules (grading L) n m))

/-! ### The five legs, pasted -/

/-- Situation [Stacks, Tag 01QH]'s map in degree `c`, with its five legs written out. -/
theorem twistComparison_eq (c : ℤ) :
    twistComparison L hL c =
      ((pbTwistIsoGood L hL c).hom ≫
          (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) c).inv ≫
          (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) c).hom ≫
          (tensorPowModuleIsoOfIsoInt X
            ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
            (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm c).hom) ≫
        (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) c).hom :=
  rfl

/-- **The pasting of the five legs' squares.**  The vertical edges are the five legs of
`twistComparisonIso` written out, nested as that composite nests them, and the six multiplications
are `pbTwistMul`; `goodTwistMul`; the multiplication
`Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackPowMulIso` of the pulled-back tensor powers
of `𝒪_{W₁}(1)`; and [Stacks, Tag 01CU]'s addition law for the tensor powers of
`(goodLift)^*𝒪_{W₁}(1)`, of `f^*𝒪_Y(1)` and of `𝓛`. -/
theorem twistComparison_mul_aux (n m : ℤ) :
    pbTwistMul L hL n m ≫
        ((pbTwistIsoGood L hL (n + m)).hom ≫
            (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) (n + m)).inv ≫
            (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) (n + m)).hom ≫
            (tensorPowModuleIsoOfIsoInt X
              ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
              (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm (n + m)).hom) ≫
          (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) (n + m)).hom =
      (((pbTwistIsoGood L hL n).hom ≫
              (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) n).inv ≫
              (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) n).hom ≫
              (tensorPowModuleIsoOfIsoInt X
                ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
                (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm n).hom) ≫
            (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) n).hom ⊗ₘ
          ((pbTwistIsoGood L hL m).hom ≫
              (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) m).inv ≫
              (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) m).hom ≫
              (tensorPowModuleIsoOfIsoInt X
                ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
                (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm m).hom) ≫
            (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) m).hom) ≫
        (tensorPowModuleAddIso X L n m).hom :=
  Stacks.Monoidal.paste5_free (pbTwistMul L hL n m) (goodTwistMul L hL n m)
    (pullbackPowMulIso (goodLift L hL) (twist (grading L) 1) n m).hom
    (tensorPowModuleAddIso X
      ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1)) n m).hom
    (tensorPowModuleAddIso X (pbTwist L hL 1) n m).hom
    (tensorPowModuleAddIso X L n m).hom
    (pbTwistIsoGood L hL n).hom (pbTwistIsoGood L hL m).hom (pbTwistIsoGood L hL (n + m)).hom
    ((Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) n).inv)
    ((Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) m).inv)
    ((Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) (n + m)).inv)
    (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) n).hom
    (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) m).hom
    (pullbackTensorPowModuleIntIso (goodLift L hL) (twist (grading L) 1) (n + m)).hom
    (tensorPowModuleIsoOfIsoInt X
      ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
      (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm n).hom
    (tensorPowModuleIsoOfIsoInt X
      ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
      (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm m).hom
    (tensorPowModuleIsoOfIsoInt X
      ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
      (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm (n + m)).hom
    (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) n).hom
    (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) m).hom
    (tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) (n + m)).hom
    (pbTwistIsoGood_mul L hL n m) (pullbackTheta_mul L hL n m)
    (pullbackTensorPowModuleIntIso_mul (goodLift L hL) (twist (grading L) 1) n m)
    (tensorPowModuleIsoOfIsoInt_mul
      ((Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) 1))
      (pbTwist L hL 1) (pbTwistIsoGood L hL 1).symm n m)
    (tensorPowModuleIsoOfIsoInt_mul (pbTwist L hL 1) L (degreeOneIso L hL) n m)

/-- **Situation [Stacks, Tag 01QH]'s map is multiplicative in an arbitrary integer bidegree.**  The
graded `𝒪_X`-algebra structure `pbTwistMul` on `⨁_{n ∈ ℤ} f^*𝒪_Y(n)`, followed by the comparison
in the degree `n + m`, is the comparisons in the degrees `n` and `m` on the two factors, followed
by the addition law `Stacks.Ample.tensorPowModuleAddIso` of [Stacks, Tag 01CU] for the tensor
powers of `𝓛`.

Together with the degreewise family `twistComparison` this makes the family a homomorphism of
sheaves of `ℤ`-graded algebras in this repository (`Stacks.SheafOfModules.GradedAlgebra.Hom`,
registered for [Stacks, Tag 0FQW]), which is exactly a degreewise family together with
multiplicativity in every bidegree; with unit preservation
(`Stacks.SectionRingVeroneseChart.pbTwistUnit_twistComparison`) the three are the `ℤ`-graded
`𝒪_X`-algebra map `⨁_{n ∈ ℤ} f^*𝒪_Y(n) ⟶ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}` the Situation equips the canonical
morphism with.

The proof is the pasting `twistComparison_mul_aux` of the five legs' squares, read at the
unfolding `twistComparison_eq` of the composite. -/
@[stacks 01QH "multiplicativity of the Situation's map in an arbitrary integer bidegree (n, m). \
With the degreewise family twistComparison this makes the family a homomorphism of sheaves of \
Z-graded algebras here (SheafOfModules.GradedAlgebra.Hom, registered for 0FQW), which is exactly \
a degreewise family plus multiplicativity in every bidegree; with unit preservation \
(pbTwistUnit_twistComparison, the extra datum of GradedAlgebra.UnitalHom) the three jointly give \
the Z-graded O_X-algebra map the Situation equips the canonical morphism with. The graded algebra \
structure on the source is pbTwistMul, Tag 01MO's multiplication of the twisting sheaves pulled \
back along the canonical morphism of Tag 01PZ and conjugated by Tag 01CD; on the target it is \
Tag 01CU's addition law"]
theorem twistComparison_mul (n m : ℤ) :
    pbTwistMul L hL n m ≫ twistComparison L hL (n + m) =
      (twistComparison L hL n ⊗ₘ twistComparison L hL m) ≫
        (tensorPowModuleAddIso X L n m).hom :=
  Stacks.Monoidal.square_of_eq_free (twistComparison_eq L hL n) (twistComparison_eq L hL m)
    (twistComparison_eq L hL (n + m)) (twistComparison_mul_aux L hL n m)

end Monoidal

end Stacks.SectionRingVeroneseChart

end
