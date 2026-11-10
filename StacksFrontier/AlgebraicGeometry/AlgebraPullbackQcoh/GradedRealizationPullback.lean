module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.UnderlyingModuleIso
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedCommutative
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction

/-!
# The algebra pullback of an ungraded realisation

Let `g : X ⟶ Y` be a morphism of schemes and `𝒜` a sheaf of `ℤ`-graded `𝒪_Y`-algebras with
commutative homogeneous multiplication. There are two ways to pull `𝒜` back to `X` and read the
result as an algebra sheaf in the sense of [Stacks, Tag 01LM]:

* realise `𝒜` as the sheaf of commutative `𝒪_Y`-algebras `⨁ₙ 𝒜ₙ`
  (`Stacks.RelativeSpec.gradedAlgebraSheaf`) and apply the *algebra* pullback
  `Stacks.AffineAlgebraEquivalence.algebraPullback`, which is the pushout
  `g⁻¹(⨁ₙ 𝒜ₙ) ⊗_{g⁻¹𝒪_Y} 𝒪_X` of sheaves of commutative rings;
* pull the graded algebra back degreewise, `Stacks.RingedSpace.pullbackGradedAlgebra`, and realise
  `⨁ₙ g^*𝒜ₙ` on `X`.

**This file constructs the comparison between them**, multiplication and unit included: the
morphism of sheaves of commutative `𝒪_X`-algebras

`Φ : (algebraPullback g).obj (⨁ₙ 𝒜ₙ) ⟶ ⨁ₙ g^*𝒜ₙ`.

It is the morphism that
`StacksFrontier/AlgebraicGeometry/SectionRingProjIso/GradedTwistAlgebra.lean`
and `StacksFrontier/AlgebraicGeometry/SectionRingProjIso/Proper.lean` record as the one thing
between
the comparisons of [Stacks, Tag 01QH] and the diagram clause of [Stacks, Tag 0EKI] — the transport
of [Stacks, Tag 0EKG]'s two left-hand entries, which are relative spectra of the twist *algebras*
over `Proj A`, to `X` along the identification `X ≅ Proj A`. Both left-hand entries are
`Stacks.RelativeSpec.gradedAlgebraSheaf` of a graded algebra and the transport goes through
`algebraPullback`, so what is needed is exactly a comparison of the two pullbacks above.

## The route

A morphism out of the algebra pullback is, by
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`, a morphism
`β : ⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)` of algebra sheaves on `Y`, and `β` is built where the realisation has
a universal property: `⨁ₙ 𝒜ₙ` is the sheafification of the presheaf of rings whose sections over
`V` are the direct sum `⨁ₙ Γ(V, 𝒜ₙ)`, so `Stacks.GradedAlgebra.totalSheafLift` reduces `β` to a
degreewise family of additive maps `Γ(V, 𝒜ₙ) ⟶ Γ(g⁻¹V, ⨁ₙ g^*𝒜ₙ)` which is multiplicative and
unital. That family is the pullback unit followed by the degree-`n` inclusion, and the two
conditions are exactly the two identities
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` and
`Stacks.RingedSpace.pullbackGradedAlgebra_one_eval`; the assembly itself is the existing
`Stacks.GradedAlgebra.totalPresheafDesc` and is not rewritten here. **No affineness is used**,
which is what distinguishes this from `Stacks.Blowup.reesComapAlgebraHom`: there the morphism of
algebra sheaves is produced from a ring homomorphism on global sections over an affine base
(`Stacks.RelativeSpec.AlgebraSheaf.algebraHom`), a route unavailable over `Proj A`.

## Main definitions

* `Stacks.GradedRealizationPullback.pbGraded`: `g^*𝒜`, the degreewise pullback, with
  `pbGraded_mul_comm` its commutativity, so that both sides of the comparison are defined.
* `Stacks.GradedRealizationPullback.inclAddHom`: **the degreewise comparison**, the pullback unit
  followed by the degree-`n` inclusion, with `inclAddHom_mul`, `inclAddHom_one` and
  `inclAddHom_naturality` the three conditions `Stacks.GradedAlgebra.totalPresheafDesc` consumes.
* `Stacks.GradedRealizationPullback.totalPresheafHom`: the comparison of the *objectwise* direct
  sums, `⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)` as a morphism of presheaves of rings.
* `Stacks.GradedRealizationPullback.ungradedPushforwardHom`: `β` as a morphism of sheaves of
  rings `⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)`, the sheafification applied once at the end.
* `Stacks.GradedRealizationPullback.pushforwardHom`: `β : ⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)`, as a morphism
  of sheaves of commutative `𝒪_Y`-algebras.
* `Stacks.GradedRealizationPullback.comparison`: **`Φ`, the adjoint transpose of `β`** — the
  comparison of the algebra pullback of the realisation with the realisation of the degreewise
  pullback.

## Main results

* `Stacks.GradedRealizationPullback.totalPresheafHom_app_incl`: the only description of the
  degreewise comparison there is — on a homogeneous section it is the pullback unit followed by
  the degree-`n` inclusion. Every computation with `β` or `Φ` goes through it.
* `Stacks.GradedRealizationPullback.totalPresheafHom_app_structureMap` and
  `ungradedPushforwardHom_ungradedStructureMap`: the compatibility with the two structure maps,
  which is what makes `β` a morphism of *algebra* sheaves and not merely of sheaves of rings.
* `Stacks.GradedRealizationPullback.comparison_app_unit`: **the handle on `Φ`** — on the unit image
  of a section of `⨁ₙ 𝒜ₙ` over `V` it is `β` on that section, hence on a homogeneous
  `x : Γ(V, 𝒜ₙ)` it is the degree-`n` inclusion of the pullback unit image of `x`.

## Invertibility

**`Φ` is invertible**, and nothing in this file is registered for any tag. The invertibility is
`Stacks.GradedRealizationPullback.isIso_comparison` in the sibling
`StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/GradedRealizationPullbackIso.lean`, packaged
as
`…comparisonIso`, which is what the diagram clause of [Stacks, Tag 0EKI] consumes.

The route there is not the stalkwise one that
`StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/Invertible.lean` takes for the module
comparison of [Stacks, Tag 01SA]. `Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap` reduces an
isomorphism of algebra sheaves to one of the underlying modules, and both underlying modules are
coproducts of the homogeneous pieces, over all of `ℤ` and with no vanishing hypothesis:
`Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule` in
`StacksFrontier/AlgebraicGeometry/Constructions/GradedAlgebraSheafCoproductInt.lean`, out of
`Stacks.RelativeSpec.gradedDirectSumIsoUnderlyingModule` and `Stacks.sheafifyDirectSumIso`. The
module pullback is a left adjoint, so it carries the coproduct to the coproduct, and the content
is that the comparison *is* that canonical isomorphism — checked one summand at a time, where the
only handle `Φ` has, `comparison_app_unit` together with `pushforwardHom_ungradedIncl`, says
exactly what the coproduct injections do.

The stalkwise route is open as well: the stalk of a coproduct of sheaves of modules is the direct
sum of the stalks, `SheafOfModules.stalkCoprodEquiv` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/AlgebraStalkUngraded.lean`, together with the stalk
of the algebra pullback (`Stacks.AlgebraPullbackQcoh.isPushout_stalk_target` and
`targetStalkLinearEquiv`), the stalk of a degreewise pullback
(`Stacks.PullbackTensorIso.pullbackStalkEquiv`, which on `1 ⊗ germ a` gives the germ of the
pullback unit image of `a`) and `TensorProduct.directSum`. It is longer, and the index type of
`stalkCoprodEquiv` is the universe of the space rather than `Type`, which `ℤ` does not inhabit for
a general universe; the coproduct route needs neither restriction.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.RingedSpace

universe u

namespace Stacks.GradedRealizationPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (𝒜 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)

/-! ### The degreewise pullback -/

/-- **`g^*𝒜`, the degreewise pullback of a sheaf of graded algebras along a morphism of schemes**:
`Stacks.RingedSpace.pullbackGradedAlgebra` at the morphism of ringed spaces underlying `g`. -/
abbrev pbGraded : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  pullbackGradedAlgebra g.toLRSHom.toShHom 𝒜

/-- **The homogeneous multiplication of `g^*𝒜` is commutative as soon as that of `𝒜` is**, so the
ungraded realisation of `g^*𝒜` is a sheaf of commutative algebras and the comparison has a
target. -/
theorem pbGraded_mul_comm
    (hc : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝒜.piece i).val.obj W)
      (b : (𝒜.piece j).val.obj W), HEq ((𝒜.mul i j).app W a b) ((𝒜.mul j i).app W b a))
    (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : ((pbGraded g 𝒜).piece i).val.obj W)
    (b : ((pbGraded g 𝒜).piece j).val.obj W) :
    HEq (((pbGraded g 𝒜).mul i j).app W a b) (((pbGraded g 𝒜).mul j i).app W b a) :=
  pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom 𝒜 hc i j W a b

/-! ### The degreewise comparison on sections of the presheaf direct sum

Everything in this section is stated at the level of `Stacks.GradedAlgebra.Total`, the objectwise
direct sum of the homogeneous pieces, where the sheafification of the ungraded realisation does not
occur.  The sheafification is applied once, at the end, by composing with its own unit, whose
naturality is free; stating the degreewise comparison against the sheafified realisation instead
makes the types of the intermediate terms contain a sheafification of a sheafification — the module
pullback is already one — and the `whnf` of those exceeds the heartbeat allowance.

The assembly of the degreewise data into a morphism of presheaves of rings is **not** written out
here: it is `Stacks.GradedAlgebra.totalPresheafDesc`, which takes exactly a natural degreewise
family of additive maps that is multiplicative and unital and is stated for a graded algebra of
presheaves of modules on an arbitrary site.
-/

/-- The degree-`n` comparison `Γ(V, 𝒜ₙ) ⟶ ⨁ₙ Γ(g⁻¹V, g^*𝒜ₙ)`: the pullback unit
`Stacks.RingedSpace.pullbackUnit`, followed by the degree-`n` inclusion into the objectwise direct
sum, as an additive map. -/
def inclAddHom (n : ℤ) (W : (Opens ↥Y)ᵒᵖ) :
    (𝒜.piece n).val.obj W →+
      (pbGraded g 𝒜).toPresheafGradedAlgebra.Total ((Opens.map g.base).op.obj W) where
  toFun x := (pbGraded g 𝒜).toPresheafGradedAlgebra.incl n
    (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) W x)
  map_zero' :=
    (congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl n)
        (show pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) W 0 = 0 from map_zero _)).trans
      ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl_zero n)
  map_add' x y :=
    (congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl n)
        (pullbackUnit_add g.toLRSHom.toShHom (𝒜.piece n) W x y)).trans
      ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl_add n
        (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) W x)
        (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) W y))

/-- **The degreewise comparison is multiplicative**: the pullback unit carries the graded product
of `𝒜` to the graded product of `g^*𝒜`
(`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit`), and the degree-`n` inclusions carry
a graded product to the ring product (`Stacks.GradedAlgebra.incl_mul_incl`). -/
theorem inclAddHom_mul (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (x : (𝒜.piece i).val.obj W)
    (y : (𝒜.piece j).val.obj W) :
    inclAddHom g 𝒜 (i + j) W ((𝒜.mul i j).app W x y) =
      inclAddHom g 𝒜 i W x * inclAddHom g 𝒜 j W y :=
  (congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl (i + j))
        (pullbackGradedAlgebra_mul_pullbackUnit g.toLRSHom.toShHom 𝒜 i j W.unop x y).symm).trans
    ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl_mul_incl i j
      (pullbackUnit g.toLRSHom.toShHom (𝒜.piece i) W x)
      (pullbackUnit g.toLRSHom.toShHom (𝒜.piece j) W y)).symm

/-- **The degreewise comparison is unital**: the unit of `g^*𝒜` is the pullback unit image of the
unit of `𝒜` (`Stacks.RingedSpace.pullbackGradedAlgebra_one_eval`). -/
theorem inclAddHom_one (W : (Opens ↥Y)ᵒᵖ) :
    inclAddHom g 𝒜 0 W (𝒜.one.eval W) = 1 :=
  (congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl 0)
        (pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom 𝒜 W.unop).symm).trans
    ((pbGraded g 𝒜).toPresheafGradedAlgebra.one_eq_incl ((Opens.map g.base).op.obj W)).symm

/-- **The degreewise comparison is natural**: the pullback unit commutes with restriction
(`Stacks.RingedSpace.pullbackUnit_restrict`) and so do the degree-`n` inclusions
(`Stacks.GradedAlgebra.totalRestrict_incl`). -/
theorem inclAddHom_naturality (U V : (Opens ↥Y)ᵒᵖ) (h : U ⟶ V) (n : ℤ)
    (x : (𝒜.piece n).val.obj U) :
    inclAddHom g 𝒜 n V (Stacks.sectionRestrict (𝒜.piece n).val h x) =
      (((Opens.map g.base).op ⋙
          (pbGraded g 𝒜).toPresheafGradedAlgebra.totalPresheaf).map h).hom
        (inclAddHom g 𝒜 n U x) :=
  (congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl n)
        (pullbackUnit_restrict g.toLRSHom.toShHom (𝒜.piece n) h x).symm).trans
    ((pbGraded g 𝒜).toPresheafGradedAlgebra.totalRestrict_incl ((Opens.map g.base).op.map h) n
      (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) U x)).symm

/-! ### The comparison as a morphism of presheaves of rings -/

/-- **The degreewise comparison as a morphism of presheaves of rings**
`⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)`, both direct sums taken objectwise.  This is the general assembly
`Stacks.GradedAlgebra.totalPresheafDesc` fed `inclAddHom` with its multiplicativity, unitality and
naturality; nothing about it is special to this situation. -/
def totalPresheafHom :
    𝒜.toPresheafGradedAlgebra.totalPresheaf ⟶
      (Opens.map g.base).op ⋙ (pbGraded g 𝒜).toPresheafGradedAlgebra.totalPresheaf :=
  𝒜.toPresheafGradedAlgebra.totalPresheafDesc (fun n W => inclAddHom g 𝒜 n W)
    (inclAddHom_mul g 𝒜) (inclAddHom_one g 𝒜) (inclAddHom_naturality g 𝒜)

/-- **The only description of the degreewise comparison**: on a homogeneous section it is the
pullback unit followed by the degree-`n` inclusion. -/
theorem totalPresheafHom_app_incl (W : (Opens ↥Y)ᵒᵖ) (n : ℤ) (x : (𝒜.piece n).val.obj W) :
    ((totalPresheafHom g 𝒜).app W).hom (𝒜.toPresheafGradedAlgebra.incl n x) =
      (pbGraded g 𝒜).toPresheafGradedAlgebra.incl n
        (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) W x) :=
  𝒜.toPresheafGradedAlgebra.totalPresheafDesc_app_incl _ _ _ _ W n x

/-- **The degreewise comparison is compatible with the two structure maps**, which is what makes
the comparison a morphism of *algebra* sheaves and not merely of sheaves of rings.

The structure map of the ungraded realisation is `r ↦ r • 1`
(`Stacks.GradedAlgebra.structureMap`), the pullback unit is semilinear over `g^♯`
(`Stacks.RingedSpace.pullbackUnit_smul`), and the unit of `g^*𝒜` is the pullback unit image of
the unit of `𝒜` (`Stacks.RingedSpace.pullbackGradedAlgebra_one_eval`). -/
theorem totalPresheafHom_app_structureMap (V : Y.Opens) (r : Y.ringCatSheaf.obj.obj (op V)) :
    ((totalPresheafHom g 𝒜).app (op V)).hom
        (𝒜.toPresheafGradedAlgebra.structureMap (op V) r) =
      (pbGraded g 𝒜).toPresheafGradedAlgebra.structureMap (op (g ⁻¹ᵁ V))
        (show X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
          sharp g.toLRSHom.toShHom (op V) r) :=
  ((congrArg (fun t => ((totalPresheafHom g 𝒜).app (op V)).hom t)
          ((congrArg (fun t => r • t)
                (𝒜.toPresheafGradedAlgebra.one_eq_incl (op V))).trans
            (𝒜.toPresheafGradedAlgebra.incl_smul 0 r (𝒜.one.eval (op V))).symm)).trans
        (totalPresheafHom_app_incl g 𝒜 (op V) 0 (r • 𝒜.one.eval (op V)))).trans
    ((congrArg ((pbGraded g 𝒜).toPresheafGradedAlgebra.incl 0)
          ((pullbackUnit_smul g.toLRSHom.toShHom (𝒜.piece 0) (op V) r
                (𝒜.one.eval (op V))).trans
            (congrArg (fun t => sharp g.toLRSHom.toShHom (op V) r • t)
              (pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom 𝒜 V).symm))).trans
      (((pbGraded g 𝒜).toPresheafGradedAlgebra.incl_smul 0
            (show X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
              sharp g.toLRSHom.toShHom (op V) r)
            ((pbGraded g 𝒜).one.eval (op (g ⁻¹ᵁ V)))).trans
        (congrArg (fun t => (show X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
              sharp g.toLRSHom.toShHom (op V) r) • t)
          ((pbGraded g 𝒜).toPresheafGradedAlgebra.one_eq_incl (op (g ⁻¹ᵁ V))).symm)))

/-! ### The comparison as a morphism of sheaves of rings -/

/-- **`β : ⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)`, the comparison as a morphism of sheaves of rings**, for an
arbitrary morphism of schemes `g : X ⟶ Y`.

`totalPresheafHom` followed by the direct image of the sheafification unit of the ungraded
realisation of `g^*𝒜` is a morphism of presheaves of rings into a sheaf, and
`Stacks.GradedAlgebra.totalSheafLift` is the universal property that turns it into a morphism out
of the ungraded realisation of `𝒜`. -/
def ungradedPushforwardHom :
    𝒜.ungradedSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} g.base).obj (pbGraded g 𝒜).ungradedSheaf :=
  𝒜.toPresheafGradedAlgebra.totalSheafLift _ _
    (totalPresheafHom g 𝒜 ≫ Functor.whiskerLeft (Opens.map g.base).op
      ((pbGraded g 𝒜).toPresheafGradedAlgebra.toTotalSheaf
        (Opens.grothendieckTopology (X : TopCat.{u}))))

/-- `β` on the sheafification unit image of a section of the objectwise direct sum is the
sheafification unit image of the degreewise comparison on that section.  This is the only
description of `β` there is, and every computation with it goes through it. -/
theorem ungradedPushforwardHom_totalUnit (V : Y.Opens)
    (z : 𝒜.toPresheafGradedAlgebra.Total (op V)) :
    ((ungradedPushforwardHom g 𝒜).hom.app (op V)).hom
        (𝒜.toPresheafGradedAlgebra.totalUnit
          (Opens.grothendieckTopology (Y : TopCat.{u})) (op V) z) =
      (pbGraded g 𝒜).toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (X : TopCat.{u})) (op (g ⁻¹ᵁ V))
        (((totalPresheafHom g 𝒜).app (op V)).hom z) :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ : 𝒜.toPresheafGradedAlgebra.totalPresheaf ⟶
        ((TopCat.Sheaf.pushforward RingCat.{u} g.base).obj
          (pbGraded g 𝒜).ungradedSheaf).obj => φ.app (op V))
      (𝒜.toPresheafGradedAlgebra.toTotalSheaf_totalSheafLift
        (Opens.grothendieckTopology (Y : TopCat.{u})) _ _))
    z

/-- **`β` on a homogeneous local section** is the degree-`n` inclusion of its pullback unit
image. -/
theorem ungradedPushforwardHom_ungradedIncl (V : Y.Opens) (n : ℤ)
    (x : (𝒜.piece n).val.obj (op V)) :
    ((ungradedPushforwardHom g 𝒜).hom.app (op V)).hom (𝒜.ungradedIncl n x) =
      (pbGraded g 𝒜).ungradedIncl n
        (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) (op V) x) :=
  (ungradedPushforwardHom_totalUnit g 𝒜 V _).trans
    (congrArg _ (totalPresheafHom_app_incl g 𝒜 (op V) n x))

/-- **`β` is compatible with the two structure maps**: the structure map of `⨁ₙ 𝒜ₙ` followed by
`β` sends a section `r` of `𝒪_Y` over `V` to the structure-map image of `g^♯ r`.  This is
`totalPresheafHom_app_structureMap` through the sheafification unit, the structure map of the
realisation being the presheaf one followed by that unit. -/
theorem ungradedPushforwardHom_ungradedStructureMap (V : Y.Opens)
    (r : Y.ringCatSheaf.obj.obj (op V)) :
    ((ungradedPushforwardHom g 𝒜).hom.app (op V)).hom
        ((𝒜.ungradedStructureMap.hom.app (op V)).hom r) =
      ((pbGraded g 𝒜).ungradedStructureMap.hom.app (op (g ⁻¹ᵁ V))).hom
        (show X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
          sharp g.toLRSHom.toShHom (op V) r) :=
  (ungradedPushforwardHom_totalUnit g 𝒜 V _).trans
    (congrArg _ (totalPresheafHom_app_structureMap g 𝒜 V r))

/-! ### The comparison as a morphism of algebra sheaves -/

section Algebra

variable (hc : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝒜.piece i).val.obj W)
  (b : (𝒜.piece j).val.obj W), HEq ((𝒜.mul i j).app W a b) ((𝒜.mul j i).app W b a))

/-- `β` as a morphism of sheaves of *commutative* rings.  The sections of both ungraded
realisations commute (`SheafOfModules.GradedAlgebra.mul_comm_ungradedSheaf`) and the lift to
`CommRingCat` keeps the carrier and the operations, so this is the same data as
`ungradedPushforwardHom`. -/
def commPushforwardHom :
    𝒜.ungradedCommSheaf hc ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj
        ((pbGraded g 𝒜).ungradedCommSheaf (pbGraded_mul_comm g 𝒜 hc)) :=
  Stacks.CommRingSheaf.sheafMap (𝒜.mul_comm_ungradedSheaf hc)
    (fun W a b => (pbGraded g 𝒜).mul_comm_ungradedSheaf (pbGraded_mul_comm g 𝒜 hc)
      (op (g ⁻¹ᵁ W.unop)) a b)
    (ungradedPushforwardHom g 𝒜)

/-- **`β : ⨁ₙ 𝒜ₙ ⟶ g_*(⨁ₙ g^*𝒜ₙ)`, as a morphism of algebra sheaves on `Y`.**

The morphism of sheaves of commutative rings is `commPushforwardHom` and the compatibility with
the two structure maps — which is what makes it a morphism of *algebra* sheaves and not merely of
sheaves of rings — is `ungradedPushforwardHom_ungradedStructureMap`. -/
def pushforwardHom :
    gradedAlgebraSheaf Y 𝒜 hc ⟶
      (algebraPushforward g).obj
        (gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc)) :=
  Under.homMk (commPushforwardHom g 𝒜 hc) (by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext
      (RingHom.ext fun r => ?_)))
    obtain ⟨V⟩ := W
    exact ungradedPushforwardHom_ungradedStructureMap g 𝒜 V r)

/-- `β` on a homogeneous local section is the degree-`n` inclusion of its pullback unit image. -/
theorem pushforwardHom_ungradedIncl (V : Y.Opens) (n : ℤ) (x : (𝒜.piece n).val.obj (op V)) :
    ((pushforwardHom g 𝒜 hc).right.hom.app (op V)).hom (𝒜.ungradedIncl n x) =
      (pbGraded g 𝒜).ungradedIncl n
        (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) (op V) x) :=
  ungradedPushforwardHom_ungradedIncl g 𝒜 V n x

/-- **`Φ`, the comparison of the algebra pullback of the ungraded realisation of `𝒜` with the
ungraded realisation of the degreewise pullback `g^*𝒜`** — a morphism of sheaves of commutative
`𝒪_X`-algebras

`Φ : g⁻¹(⨁ₙ 𝒜ₙ) ⊗_{g⁻¹𝒪_Y} 𝒪_X ⟶ ⨁ₙ g^*𝒜ₙ`,

for an arbitrary morphism of schemes `g : X ⟶ Y` and an arbitrary sheaf of graded `𝒪_Y`-algebras
with commutative homogeneous multiplication.  It is the adjoint transpose of `pushforwardHom`
across the base-change adjunction for algebra sheaves,
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`; the pullback is the one a
relative spectrum over `X` consumes and the one [Stacks, Tag 01LX] part (2) produces, not the
degreewise module pullback. -/
def comparison :
    (algebraPullback g).obj (gradedAlgebraSheaf Y 𝒜 hc) ⟶
      gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm (pushforwardHom g 𝒜 hc)

/-- **The adjunction identity defining `Φ`**: the unit of the base-change adjunction for algebra
sheaves followed by the direct image of `Φ` is `β`. -/
theorem unit_comp_map_comparison :
    (algebraPullbackPushforwardAdjunction g).unit.app (gradedAlgebraSheaf Y 𝒜 hc) ≫
        (algebraPushforward g).map (comparison g 𝒜 hc) =
      pushforwardHom g 𝒜 hc :=
  (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g)
      (gradedAlgebraSheaf Y 𝒜 hc)
      (gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc))
      (comparison g 𝒜 hc)).symm.trans
    (Equiv.apply_symm_apply
      ((algebraPullbackPushforwardAdjunction g).homEquiv (gradedAlgebraSheaf Y 𝒜 hc)
        (gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc))) _)

/-- **`Φ` on the unit image of a section of `⨁ₙ 𝒜ₙ` over `V` is `β` on that section.** This is the
only handle on `Φ` there is; on a homogeneous `x : Γ(V, 𝒜ₙ)` the right-hand side is the degree-`n`
inclusion of the pullback unit image of `x`, by `pushforwardHom_ungradedIncl`. -/
theorem comparison_app_unit (V : Y.Opens)
    (b : (gradedAlgebraSheaf Y 𝒜 hc).right.obj.obj (op V)) :
    ((comparison g 𝒜 hc).right.hom.app (op (g ⁻¹ᵁ V))).hom
        ((((algebraPullbackPushforwardAdjunction g).unit.app
          (gradedAlgebraSheaf Y 𝒜 hc)).right.hom.app (op V)).hom b) =
      ((pushforwardHom g 𝒜 hc).right.hom.app (op V)).hom b := by
  refine Eq.trans (show _ = (ConcreteCategory.hom
      ((((algebraPullbackPushforwardAdjunction g).unit.app (gradedAlgebraSheaf Y 𝒜 hc) ≫
        (algebraPushforward g).map (comparison g 𝒜 hc)).right).hom.app (op V))) b
      from rfl) ?_
  exact congrArg (fun t : gradedAlgebraSheaf Y 𝒜 hc ⟶
      (algebraPushforward g).obj
        (gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc)) =>
    (ConcreteCategory.hom (t.right.hom.app (op V))) b)
    (unit_comp_map_comparison g 𝒜 hc)

end Algebra

end Stacks.GradedRealizationPullback

end
