module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackTensorPowIntBidegree
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackTwistRestrictMul
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.IntegerTwistBidegree
public import StacksFrontier.AlgebraicGeometry.SectionRingVeroneseChart.IntegerDegree

/-!
# The twist leg of the Veronese-chart comparison, pulled back to `X`

`Stacks.SectionRingVeroneseChart.twistComparisonIso` is a composite of five isomorphisms, and the
multiplicativity of each of the five in an arbitrary integer bidegree is what makes its forward
map `twistComparison` a map of `ℤ`-graded `𝒪_X`-algebras rather than a degreewise family.  (The
map of Situation [Stacks, Tag 01QH] itself is Tag 01NK's `θ`,
`Stacks.SectionRingProjMorphism.Theta.projThetaUnital`; `twistComparison` is not proved equal to
it.)
Three of the five already have their integer-bidegree square — the twist leg on `W₁`
(`Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul`), the pullback leg
(`Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackTensorPowModuleIntIso_mul`) and the
transport leg, used twice
(`Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_mul`).  **This file
supplies the square for the second of the two structural legs**, the pullback along the lift
through [Stacks, Tag 01MU]'s open `W₁` of the twist leg's square, together with the machinery that
makes it a retyping rather than a new chase.

## Main definitions

* `Stacks.SectionRingVeroneseChart.goodTwistMul`: **the multiplication of
  `⨁_{n ∈ ℤ} (goodLift)^*𝒪_{W₁}(n)`**, the canonical multiplication of the twists of
  [Stacks, Tag 01MO] read on `W₁` and conjugated by [Stacks, Tag 01CD] along the lift.

## Main results

* `Stacks.SectionRingVeroneseChart.pullbackTheta_mul`: **the second structural leg's square** —
  the pullback along the lift through `W₁` of
  `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul`, in an arbitrary integer bidegree.
* `Stacks.Monoidal.pullback_mul_square`: **`f^*` carries a bidegree square to a bidegree square**,
  the two multiplications being conjugated by [Stacks, Tag 01CD].  This is what makes the second
  structural leg a retyping of `theta_mul` rather than a new chase, and it is stated for an
  arbitrary morphism of schemes and an arbitrary multiplication on the base.
* `Stacks.Monoidal.pullback_mul_eqToHom`: the multiplications induced on the pullbacks along two
  *equal* morphisms agree through the transports along the equality.  This is the step the first
  structural leg needs, `Stacks.SectionRingVeroneseChart.pbTwistIsoGood` being the composition law
  for pullback preceded by exactly such a transport.
* `Stacks.Monoidal.paste_squares_free`, `invert_square_free`, `inv_nat_free`,
  `transport_square_free`, `id_both_free`: the free-shape steps the above are assembled from, and
  the ones a composite of bidegree squares is pasted with.

## What is not done here

**Both remaining pieces are supplied, in
`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean`.**  The first
structural leg's square is `Stacks.SectionRingVeroneseChart.pbTwistIsoGood_mul` and the pasting of
the five is `Stacks.SectionRingVeroneseChart.twistComparison_mul_aux`, whence
`Stacks.SectionRingVeroneseChart.twistComparison_mul`: `twistComparison` is
multiplicative in an arbitrary integer bidegree.  Two mechanical obstacles arise; they are
resolved as follows, as that file's implementation notes record.

* The canonical multiplication of the twisting sheaves is ascribed at the
  `Stacks.RelativeVeryAmple.tensorModules` spelling as
  `Stacks.AlgebraicGeometry.TwistTensor.twistMulModules`.  Ascribing it at `⊗` instead does *not*
  work: the type ascription leaves the object at the `SheafOfModules (projStructureRing 𝒮)`
  spelling and instance search then fails outright for `MonoidalCategoryStruct` there.
* The pasting does not exceed the heartbeat allowance once every definitional unfolding is isolated
  into its own `rfl` lemma and the two free-shape movers `Stacks.Monoidal.square_of_eq_free` and
  `square_transfer_free` take those unfoldings as inputs; and the two halves of the first leg's
  square are pasted by `Stacks.Monoidal.pullbackComp_mul_eqToHom`, which does it with the schemes,
  the morphisms and the modules all variables.  Pasting them at the concrete objects — by
  `paste_squares_free` with the `eqToHom`s written out, with the arguments supplied explicitly or
  left to unification, or in one `exact` against the compact statement — exceeds it in `isDefEq`
  and in `whnf` respectively.  All of that is measurement, at 200 000 heartbeats.

No Stacks registration is carried here.

## Implementation notes

**Every statement here is proved by term-level rearrangement, never by `rw` on the concrete
goal.**  The goals mention both spellings of the structure ring sheaf of a scheme — the one
`AlgebraicGeometry.Scheme.Modules` records and the one
`RingedSpaceModuleAdjunction.modulePullback` does — so they are not type-correct at the
`implicit` transparency level and neither `rw` nor `simp only` fires on them.  The free-shape
lemmas of `Stacks.Monoidal` below are each one step of a square, with every object and morphism a
variable, which is the discipline of
`StacksFrontier/AlgebraicGeometry/TwistTensor/PullbackTwistRestrictMul.lean` and of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean`.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.GoodOpenIntTwist (goodOpen twist theta twistMulIso)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.AlgebraicGeometry.ThetaMul
open Stacks.AlgebraicGeometry.PullbackTensorPowInt

namespace Stacks.Monoidal

section Free

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **Two bidegree squares in a row paste to one.**  The horizontal edges of the pasted square are
the composites of the two squares', one factor of the tensor product at a time. -/
theorem paste_squares_free {A B C A' B' C' A'' B'' C'' : D}
    (u : A ⊗ B ⟶ C) (u' : A' ⊗ B' ⟶ C') (u'' : A'' ⊗ B'' ⟶ C'')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (c' : C' ⟶ C'')
    (h : u ≫ c = (a ⊗ₘ b) ≫ u') (h' : u' ≫ c' = (a' ⊗ₘ b') ≫ u'') :
    u ≫ c ≫ c' = ((a ≫ a') ⊗ₘ (b ≫ b')) ≫ u'' := by
  rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]

/-- **A bidegree square with its three vertical edges inverted.**  The two multiplications change
places: the square for a family of isomorphisms read in the other direction. -/
theorem invert_square_free {A B C A' B' C' : D} (a : A ≅ A') (b : B ≅ B') (c : C ≅ C')
    (u : A ⊗ B ⟶ C) (u' : A' ⊗ B' ⟶ C')
    (h : u ≫ c.hom = (a.hom ⊗ₘ b.hom) ≫ u') :
    u' ≫ c.inv = (a.inv ⊗ₘ b.inv) ≫ u := by
  rw [Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

omit [MonoidalCategory D] in
/-- A composite with an endomorphism known to be an identity appended, and the identity tensor
product of two identities prepended. -/
theorem id_both_free {A B : D} (x : A ⟶ B) (i : B ⟶ B) (j : A ⟶ A)
    (hi : i = CategoryStruct.id B) (hj : j = CategoryStruct.id A) : x ≫ i = j ≫ x := by
  rw [hi, hj, Category.id_comp, Category.comp_id]

omit [MonoidalCategory D] in
/-- A square whose two parallel edges are isomorphisms, with both of them inverted and the
horizontal edges kept.

This is `Stacks.Algebraization.inv_comp_eq_comp_inv` at the `CategoryTheory.Iso.inv` spelling of
the inverse rather than the `CategoryTheory.inv` one.  The two are not interchangeable here: `inv`
is not an exposed definition under the module system, and in the categories of sheaves of modules
of a scheme the `IsIso` instance for the forward map of an `Iso` is not found — both spellings of
the structure ring sheaf are in play and the instance is keyed on one of them. -/
theorem inv_nat_free {A B E G : D} (e : A ≅ B) (x : A ⟶ E) (y : B ⟶ G) (e' : E ≅ G)
    (h : x ≫ e'.hom = e.hom ≫ y) : e.inv ≫ x = y ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [MonoidalCategory D] in
/-- **One square out of a multiplication that a functor has been applied to**, with every object
and morphism a variable: the two multiplications are `d ≫ p` and `d' ≫ p'`, the functor's images
of the two multiplications on the base conjugated by the comparison of [Stacks, Tag 01CD], and the
three inputs are the splitting of the functor's image of the base square and the naturality of the
comparison. -/
theorem transport_square_free {A B E G K L : D}
    (d : A ⟶ B) (p : B ⟶ E) (q : E ⟶ G) (r : B ⟶ G) (s : B ⟶ K) (p' : K ⟶ G)
    (t : A ⟶ L) (d' : L ⟶ K)
    (hpq : p ≫ q = r) (hr : r = s ≫ p') (hcomm : d ≫ s = t ≫ d') :
    (d ≫ p) ≫ q = t ≫ d' ≫ p' := by
  rw [Category.assoc, hpq, hr, ← Category.assoc, hcomm, Category.assoc]

end Free

/-! ### Pullback carries a bidegree square to a bidegree square -/

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

/-- **`f^*` carries a bidegree square to a bidegree square.**  Both multiplications are conjugated
by the comparison of [Stacks, Tag 01CD]: a morphism `u : A ⊗ B ⟶ C` of `𝒪_S`-modules induces
`f^*A ⊗ f^*B ⟶ f^*C` by inverting the comparison and applying `f^*`.  If a degreewise family of
isomorphisms carries one such `u` to another on `S`, then its pullback carries the induced
multiplication to the induced multiplication.

This is naturality of [Stacks, Tag 01CD] in both arguments
(`Stacks.Algebraization.pullbackTensorModulesIso_naturality`) together with the functoriality of
`f^*`; no coherence of the monoidal structure of `f^*` is used, so no monoidal structure on the
functor has to be chosen. -/
theorem pullback_mul_square {X S : Scheme.{u}} (g : X ⟶ S) {A B C A' B' C' : S.Modules}
    (u : A ⊗ B ⟶ C) (u' : A' ⊗ B' ⟶ C') (a : A ≅ A') (b : B ≅ B') (c : C ⟶ C')
    (h : u ≫ c = (a.hom ⊗ₘ b.hom) ≫ u') :
    ((pullbackTensorModulesIso g A B).inv ≫ (Scheme.Modules.pullback g).map u) ≫
        (Scheme.Modules.pullback g).map c =
      ((Scheme.Modules.pullback g).map a.hom ⊗ₘ (Scheme.Modules.pullback g).map b.hom) ≫
        ((pullbackTensorModulesIso g A' B').inv ≫ (Scheme.Modules.pullback g).map u') :=
  transport_square_free _ _ _ _ _ _ _ _
    ((Scheme.Modules.pullback g).map_comp u c).symm
    ((congrArg (Scheme.Modules.pullback g).map h).trans
      ((Scheme.Modules.pullback g).map_comp _ _))
    (inv_nat_free (pullbackTensorModulesIso g A B) _ _ (pullbackTensorModulesIso g A' B')
      ((((congrArg (fun z ↦ (Scheme.Modules.pullback g).map z ≫
                (pullbackTensorModulesIso g A' B').hom)
            (Stacks.Algebraization.tensorModulesMap_hom_eq_tensorHom S a b)).symm.trans
          (Stacks.Algebraization.pullbackTensorModulesIso_naturality g a.hom b.hom)).trans
        (congrArg (fun z ↦ (pullbackTensorModulesIso g A B).hom ≫ z)
          (Stacks.Algebraization.tensorModulesMap_hom_eq_tensorHom X
            ((Scheme.Modules.pullback g).mapIso a) ((Scheme.Modules.pullback g).mapIso b))))))

/-- **The multiplication induced on the pullbacks along two equal morphisms agree**, through the
transports along the equality.  `Stacks.SectionRingVeroneseChart.pbTwistIsoGood` is the
composition law for pullback preceded by exactly such a transport, the two morphisms being the
canonical morphism of [Stacks, Tag 01PZ] and its factorisation through [Stacks, Tag 01MU]'s open
`W₁`. -/
theorem pullback_mul_eqToHom {X S : Scheme.{u}} {φ ψ : X ⟶ S} (e : φ = ψ) {A B C : S.Modules}
    (u : A ⊗ B ⟶ C) :
    ((pullbackTensorModulesIso φ A B).inv ≫ (Scheme.Modules.pullback φ).map u) ≫
        eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj C) e) =
      (eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj A) e) ⊗ₘ
          eqToHom (congrArg (fun χ : X ⟶ S ↦ (Scheme.Modules.pullback χ).obj B) e)) ≫
        ((pullbackTensorModulesIso ψ A B).inv ≫ (Scheme.Modules.pullback ψ).map u) := by
  cases e
  exact id_both_free _ _ _ (eqToHom_refl _ _)
    ((MonoidalCategory.tensorHom_id (CategoryStruct.id _) _).trans
      (MonoidalCategory.id_whiskerRight _ _))

end Stacks.Monoidal

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

/-! ### The pulled-back multiplication of the twists on `W₁` -/

/-- **The multiplication of the pullbacks of the twists along the lift through `W₁`**, which is
the multiplication `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso` of [Stacks, Tag 01MO]
read on [Stacks, Tag 01MU]'s open `W₁` and conjugated by [Stacks, Tag 01CD] along `goodLift`.
This is the graded `𝒪_X`-algebra structure the first structural leg of
`Stacks.SectionRingVeroneseChart.pbTwistIsoTensorPow` lands in. -/
def goodTwistMul (n m : ℤ) :
    (Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) n) ⊗
        (Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) m) ⟶
      (Scheme.Modules.pullback (goodLift L hL)).obj (twist (grading L) (n + m)) :=
  (pullbackTensorModulesIso (goodLift L hL) (twist (grading L) n)
      (twist (grading L) m)).inv ≫
    (Scheme.Modules.pullback (goodLift L hL)).map (twistMulIso (grading L) n m).hom

/-! ### The second structural leg -/

/-- **The second structural leg's square: the pullback along the lift through `W₁` of the twist
leg's square.**  `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul` is the bidegree square on
`W₁` for the comparison `𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)` in an arbitrary integer bidegree;
`Stacks.Monoidal.invert_square_free` reads it with the three isomorphisms inverted, and
`Stacks.Monoidal.pullback_mul_square` pulls it back. -/
theorem pullbackTheta_mul (n m : ℤ) :
    goodTwistMul L hL n m ≫
        (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) (n + m)).inv =
      ((Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) n).inv ⊗ₘ
          (Scheme.Modules.pullback (goodLift L hL)).map (theta (grading L) m).inv) ≫
        (pullbackPowMulIso (goodLift L hL) (twist (grading L) 1) n m).hom := by
  rw [pullbackPowMulIso_hom, goodTwistMul]
  exact Stacks.Monoidal.pullback_mul_square (goodLift L hL)
    (twistMulIso (grading L) n m).hom
    (Stacks.AlgebraicGeometry.GoodOpenIntTwist.tpowAdd (grading L) n m).hom
    (theta (grading L) n).symm (theta (grading L) m).symm
    (theta (grading L) (n + m)).inv
    (Stacks.Monoidal.invert_square_free (theta (grading L) n) (theta (grading L) m)
      (theta (grading L) (n + m))
      (Stacks.AlgebraicGeometry.GoodOpenIntTwist.tpowAdd (grading L) n m).hom
      (twistMulIso (grading L) n m).hom
      (Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul (grading L) n m))

end Monoidal

end Stacks.SectionRingVeroneseChart

end
