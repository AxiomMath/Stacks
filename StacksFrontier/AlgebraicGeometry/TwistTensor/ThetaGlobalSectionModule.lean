module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceQuasicoherentModule
public import StacksFrontier.AlgebraicGeometry.Picard.Group.TensorConstraints
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobalSectionPower

/-!
# The twisted sections of a module and the graded section module of Tag 01CV, degree by degree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring covered in degree one, `X = Proj S`, let `d` be a degree
with `𝒪_X(d)` invertible, and let `ℱ` be a sheaf of `𝒪_X`-modules. Two graded modules of twisted
global sections of `ℱ` are in play.

* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistSectionModule 𝒮 ℱ = ⨁_{m ≥ 0} Γ(X, ℱ(m))`,
  the graded `S`-module of [Stacks, Tag 03GM], whose degree-`m` piece is the global sections of
  `ℱ ⊗ 𝒪_X(m)`.
* `Stacks.SheafOfModules.sectionModule 𝒪 h𝒪 L ℱ = ⨁_{n ∈ ℤ} Γ(X, ℱ ⊗ L^{⊗ n})` of
  [Stacks, Tag 01CV], at `L = 𝒪_X(d)`, which is the module [Stacks, Tag 01PW] localizes.

This file compares them **degree by degree**: the degree-`n` piece of the second is the
degree-`n d` piece of the first.

Nothing but bookkeeping happens. `twistSheafOfModules` *is*
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` applied to `ℱ` and a twisting sheaf
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`), and the degree-`n` piece of
Tag 01CV's module is the same construction applied to `ℱ` and
`Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L n`, so the two differ only in the second
tensor factor and
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` identifies those. Whiskering it by `ℱ`
is `Stacks.SheafOfModules.tensorSheafMapIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.ThetaGlobal.twistTensorPowerIso`: **`ℱ ⊗ 𝒪(d)^{⊗ n} ≅ ℱ(dn)`**, in
  every integer degree, with the power taken at the spelling Tag 01CV's module is graded by.
* `Stacks.AlgebraicGeometry.ThetaGlobal.topIsoTerminal`: the open `⊤` and the categorical
  terminal object of `Opens X` are isomorphic. Tag 03GM's twisted sections are taken over `⊤` and
  Tag 01CV's over `⊤_`, and the two are **not** definitionally equal here: the terminal object is
  produced by `CategoryTheory.Limits.getLimitCone`, whose definition this module does not expose.
* `Stacks.AlgebraicGeometry.ThetaGlobal.twistSectionsEquiv`: **the degreewise comparison of the
  two graded modules**, `Γ(X, ℱ ⊗ 𝒪(d)^{⊗ m}) ≃+ Γ(X, ℱ(d m))`.

## What is not done

The comparison is of the **carriers in each degree**. Two things are still owed before the two
graded modules are compared as graded modules, and both are about the trivializing section rather
than about the twists. **Neither is an induction against `theta`'s recursion alone**; where the
work actually sits is recorded after them.

1. that `twistSectionsEquiv` carries the action of `f ∈ 𝒮 d` on `Γ(X, ℱ(m d))` to the action of
   the degree-one element of Tag 01CV's section ring that `f` determines, and
2. that it carries "multiply by the trivializing section `f ^ n` of `𝒪(n d)`"
   (`Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection`) to "tensor with `sⁿ`"
   (`Stacks.SheafOfModules.tensorSectionAtOpen` at `Stacks.SheafOfModules.sectionPower`).

With those two, the hypotheses of
`Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degreewise` are met and
Tag 03GM's local bijectivity follows from [Stacks, Tag 01PW] part (2) through
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.bijective_chartHom_of_degreewise`.

**Part (2) of Tag 01PW is proved, so that side of the reduction owes nothing.** It is
`Stacks.SheafOfModules.sectionLocalizationMap_bijective`, carrying `@[stacks 01PW "part (2)"]`
at `[CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]`
(`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`), and it
is already read on a chart of `Proj 𝒮` by `bijective_sectionLocalizationMap_degreeSection` in
`Stacks.AlgebraicGeometry.ProjChartNonvanishingOpen`, whose nonvanishing open is identified
with `D₊(f)` in the same module. That is exactly the data
`g`, `hg`, `hgbij` of `bijective_chartHom_of_degreewise`. What is **not** in the tree is the
family `ψ` itself — `toSectionModule` below is defined on the degree-`d m` summand
`twistSections 𝒮 ℱ (d * m)` and not on `twistSectionModule 𝒮 ℱ`, so the additive maps
`ψ n : twistSectionModule 𝒮 ℱ →+ sectionModule …` that the criterion asks for, and with them
`hψmem`, `hψsurj` and `hψinj`, are plumbing still to be written around
`twistSectionsEquiv`; the two statements above are what `hψpow` and `hcomm` need, and they are
the only *mathematics* outstanding. `bijective_chartHom_of_degreewise` is applied nowhere in
the tree as of this writing.

**Where the work sits.** Both statements compare an action defined by *multiplying a local
homogeneous fraction* with one defined by *tensoring and then applying a multiplication
isomorphism*. The two sides are these:

* Tag 03GM's action is `Stacks.AlgebraicGeometry.ProjTwistSectionModule.gsmul`, the value on
  global sections of the morphism `ProjTwistSectionModule.twistMul`, which is
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap (𝟙 ℱ)` applied to
  `ProjTwistSectionModule.homogeneousMul` — `associatedModuleSheafMap` of multiplication by the
  scalar. It does **not** go through `twistMultiplicationIso` (Equation 01MO) nor through Tag
  03GJ's `twistSheafMultiplicationMap`.
* Tag 01CV's action is `Stacks.SheafOfModules.sectionModuleAction`, which braids the scalar past
  `ℱ`, applies `Stacks.SheafOfModules.TensorPower.coherentMulIso` and reindexes, all applied to
  `Stacks.SheafOfModules.tensorGlobalSection` — the sheafification unit on a pure tensor. The
  `Module` instance carrying it is `Classical.choice`, so its only handle is the `smul_eq` field
  of `Stacks.SheafOfModules.chosenModuleStructure`.

**Both sides are already computed on a pure tensor of sections, and the section-level formula
for the monoidality of sheafification is neither needed nor available.** That formula, listed
under "What is not done here" in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingComparison.lean`, is not on the
path, for three reasons.

* Neither side is stated against the localized tensor product `⊗` whose monoidality isomorphism
  that formula is about. Both are stated against
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the tensor product *sheaf*, every
  structural isomorphism of which has a section-level formula already:
  `Stacks.SheafOfModules.tensorSections_tensorMapAt`, `tensorSections_leftUnitorAt`,
  `tensorSections_rightUnitorAt`, `tensorSections_braidingAt`, `tensorSections_associatorAt` and
  `tensorSections_tensorProductIsoAt`, all in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistSectionRing.lean`.
* Tag 01CV's action is therefore already computed on a pure tensor. It is the value on global
  sections of a *morphism of sheaves*, `Stacks.SheafOfModules.TwistAction.actionOf`
  (`Stacks.SheafOfModules.TwistAction.actionOf_app_top` in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistActionMorphism.lean`), and
  `Stacks.SheafOfModules.twistActionHom_pure` evaluates that morphism on
  `tensorSectionsAt x y` as `tensorSectionsAt x (tensorPowerMulSectionAt … y)` — proved from
  exactly the six formulas above, with no appeal to the monoidality isomorphism.
* Tag 03GM's action is likewise computed on a pure tensor, by
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection`, which
  is already what `twistMul_one`, `twistMul_mul` and `twistMul_add` below are proved by.

So `ℱ` drops out of both sides by hom-extensionality
(`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`), and what the two statements
reduce to is a comparison **on the twisting sheaves alone**: that `thetaSectionPower` carries the
Laurent multiplication of [Stacks, Tag 01CU] by the `n`-th power of the global section `f / 1` to
`homogeneousMul` by `f ^ n`.

For that comparison the ingredients are also in the tree, and the factor of `thetaSectionPower`
that compares the two constructions of the tensor powers is now crossed:
`Stacks.PowerFamilyBridge.natIso` — which `thetaSectionPower`, hence `twistSectionsEquiv`, is
built from — is identified with `Stacks.SheafOfModules.Invertible.tensorPowerCompare`, whose
multiplicativity on local sections is proved, by
`Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare` in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/PowerCompareAgreement.lean`, so that
`Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare` is available for the *first*
factor of `thetaSectionPower` in nonnegative degree. And the multiplicativity square of the
comparison family in an **arbitrary** bidegree is already proved, with the whole degree-crossing
argument written out: `Stacks.AlgebraicGeometry.ThetaMul.theta_mul` and `thetaNat_mul`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean`), with
`thetaInt_mul_zero` and `thetaInt_mul_natCast` (`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerMul.lean`) at the integer
spelling, `Stacks.AlgebraicGeometry.ThetaMul.mulSections_eq_tensorPowModuleAddIso`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaSectionMul.lean`) on honest global sections, and
`Stacks.AlgebraicGeometry.ThetaMul.thetaNat_inv_mul` together with
`twistMulIsoVeronese_hom_tmul_restrictedDegreeSection`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/UniversalVeroneseSections.lean`) reading it on the sections `a / 1` attached to homogeneous
elements — which is the template the statements above want.

Those are all stated for the degree-open comparison family
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` on
`AlgebraicGeometry.Proj.degreeOpen 𝒮 d`, not for the global family of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaGlobal.lean` that `thetaSectionPower` is built
from. **The bidegree-`(n, m)` square for the global family is proved as well**, in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaGlobalMultiplicativity.lean`:
`Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_mul` and `thetaNat_mul`, out of the global
analogues of the three laws of the canonical multiplication —
`Stacks.AlgebraicGeometry.ThetaGlobalMul.twistMulIso_assoc`, `twistMulIso_zero_left` and
`twistMulIso_zero_right` — together with the object-free inductive skeleton of
`ThetaMultiplicativity.lean` (`unit_tensorHom_cancel`, `tensorHom_unit_square`, `square_step`,
which are shared, not copied). Those three laws are **not** transported from `U_d`: on `Proj 𝒮`
the three laws of the canonical multiplication map itself are already proved in arbitrary integer
degrees over an arbitrary graded ring and with no covering hypothesis
(`Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc`, `one_twistMul` and `twistMul_one`), so the
induction re-runs globally and the pullback along the open immersion never enters.

**The passage from that square to `thetaSectionPower` itself is made, on honest global sections,
in every pair of nonnegative degrees**:
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_mulBilinear`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaGlobalSectionMultiplicativity.lean`) carries
`Stacks.SheafOfModules.TensorPower.mulBilinear` — the multiplication of the Laurent algebra of
[Stacks, Tag 01CU] that the graded section ring of Tag 01CV is built from — to the canonical
multiplication of the twists of Equation 01MO. The first factor of `thetaSectionPower`,
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`, is crossed there by
`Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear` through
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_natCast`, and the integer extension does
not enter at all: in a nonnegative degree `thetaInt` *is* the comparison built by recursion, and
both statements above are indexed by natural numbers.

What the two statements still need beyond that square is the trivializing section itself — the
**keystone**

  `thetaSectionPower 𝒮 hcover d n` carries `Stacks.SheafOfModules.sectionPower` of the global
  section `f / 1` to the global section `degreeSection 𝒮 (d * n) (f ^ n)` of `𝒪(dn)`

— and the whiskering of the square by `ℱ`, which is what carries it from the twisting sheaves to
the two actions above. Once the keystone holds, `trivializingSection` is reached with no further
work: the trivializing section of `𝒪(nd)` on `D₊(f)` *is* the restriction of
`degreeSection 𝒮 (n * d) (f ^ n)`, at arbitrary `d` and arbitrary `n : ℕ`, by
`Stacks.AlgebraicGeometry.ProjTrivialization.powSection_eq_trivializingSection`.

The keystone is an induction on `n` against `thetaSectionPower_mulBilinear`, and it has three
inputs. Two are now in the tree and one is not.

* The multiplication leg — that the canonical multiplication of the twists carries the pure
  tensor of two `degreeSection`s to the `degreeSection` of the product, in the `twistMulModules`
  and `Stacks.SheafOfModules.tensorSectionsAt` spelling in which
  `thetaSectionPower_mulBilinear` states its right-hand side — is
  `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulModules_degreeSection`
  (`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaGlobalDegreeSection.lean`). Pointwise it is
  `a / 1 · b / 1 = ab / 1`; no transport along `d · n = n · d` appears.
* The powers of the section are `Stacks.SheafOfModules.sectionPower`, whose addition law against
  `Stacks.SheafOfModules.sectionRingMul` is the shape `thetaSectionPower_mulBilinear` applies to;
  it is proved in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingSections.lean` as
  `sectionPower_add` but is `private` there, so a consumer outside that module has to make it
  public rather than restate it, together with `sectionPower_zero` and `sectionPower_one`. The
  passage from `sectionRingMul` to `Stacks.SheafOfModules.TensorPower.mulBilinear` is the
  reindexing isomorphism at `(n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ)`, whose two ends are
  definitionally the same object, so `Stacks.SheafOfModules.TensorPower.heq_reindex` crosses it.
* **The base case `n = 1` is what is genuinely absent.** It asks that
  `thetaSectionPower 𝒮 hcover d 1` be the canonical identification of the first tensor power with
  `𝒪(d)`, that is that
  `Stacks.PowerFamilyBridge.tensorPowerModuleIso` in degree one carry
  `Stacks.SheafOfModules.TensorPower.tensorPowerOneIso` to
  `Stacks.Ample.tensorPowModuleOneIso`; the `theta` factor is already pinned down by
  `Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_one_eq`. `Stacks.PowerFamilyBridge.natIso_succ`
  reduces it to the two families' unit laws at exponent zero, and **no lemma in
  `StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/` relates either `OneIso` to its `SuccIso` and
  `ZeroIso`**, so those unit laws have to be proved first. Note that
  `Stacks.ProjTwistSection.homogeneousSection_eval_eq_trivializingSection`, which an earlier
  version of this note offered as the base case, is *not* it: that statement is about the
  trivializing section on `D₊(f)` and says nothing about either tensor-power family.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.AlgebraicGeometry.ProjTwistSectionModule (twistSections)

universe u w

namespace Stacks.AlgebraicGeometry.ThetaGlobal

-- The proof-only imports provide another terminal-object instance. Retain the instance chosen
-- when Tag 01CV's section module and the statements of Tag 01PW were elaborated, as
-- `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingSections.lean` does.
attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover)

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)
  [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))]

/-- The sheaf of rings the graded section module of Tag 01CV is taken over, for `X = Proj 𝒮`. -/
abbrev projSiteRing := Stacks.SheafOfModules.sectionSiteRing (AlgebraicGeometry.Proj 𝒮)

/-- The sheaf condition on `Stacks.AlgebraicGeometry.ThetaGlobal.projSiteRing`. -/
abbrev projSiteSheaf := Stacks.SheafOfModules.sectionSiteSheaf (AlgebraicGeometry.Proj 𝒮)

variable (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))

/-- **`ℱ ⊗ 𝒪(d)^{⊗ n} ≅ ℱ(dn)`**, with the tensor power taken at the spelling the graded section
module of Tag 01CV is graded by: the twist comparison
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` whiskered by `ℱ`.

The left-hand side is the degree-`n` summand of
`Stacks.SheafOfModules.sectionModule` at `L = 𝒪(d)` and the right-hand side is the degree-`dn`
twist of Tag 03GM, both being `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of `ℱ`
against a sheaf of modules; only the second factor moves. -/
def twistTensorPowerIso (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projSiteRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projSiteRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projSiteSheaf 𝒮))⟩).obj (F)).obj
        ((Stacks.SheafOfModules.TensorPower.tensorPower (projSiteRing 𝒮) (projSiteSheaf 𝒮)
          (twist 𝒮 (d : ℤ)) n))) ≅
      twistSheafOfModules 𝒮 F ((d : ℤ) * n) :=
  Stacks.SheafOfModules.tensorSheafMapIso _ _ (Iso.refl F) (thetaSectionPower 𝒮 hcover d n)

/-- `Stacks.AlgebraicGeometry.ThetaGlobal.twistTensorPowerIso` with the twist degree spelled as
the natural number `d * m`, which is the degree at which Tag 03GM's graded module has its
summands. -/
def twistTensorPowerIsoNat (m : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projSiteRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projSiteRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projSiteSheaf 𝒮))⟩).obj (F)).obj
        ((Stacks.SheafOfModules.TensorPower.tensorPower (projSiteRing 𝒮) (projSiteSheaf 𝒮)
          (twist 𝒮 (d : ℤ)) (m : ℤ)))) ≅
      twistSheafOfModules 𝒮 F ((d * m : ℕ) : ℤ) :=
  twistTensorPowerIso 𝒮 hcover d F (m : ℤ) ≪≫
    eqToIso (congrArg (twistSheafOfModules 𝒮 F) (Nat.cast_mul d m).symm)

/-- **The open `⊤` is the categorical terminal object of `Opens X`**, up to the unique
isomorphism between two terminal objects. Tag 03GM's twisted global sections are taken over `⊤`
and Tag 01CV's over `⊤_`; the two are not definitionally equal in this module, because the
terminal object comes from `CategoryTheory.Limits.getLimitCone`, whose definition is not
exposed here. -/
def topIsoTerminal :
    (⊤ : Opens (AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace) ≅
      ⊤_ (Opens (AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace) :=
  isTerminalTop.uniqueUpToIso terminalIsTerminal

/-- Restricting along an isomorphism of objects of the site and back is the identity. Stated with
the site, the sheaf of rings, the presheaf of modules and the isomorphism all free, so that it
applies by `exact` at default transparency: the two spellings of the space underlying `Proj 𝒮`
make the expanded goal ill-typed at `implicit` transparency, where `rw` works. -/
theorem map_op_roundtrip {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {U V : C} (e : U ≅ V) (x : P.obj (op V)) :
    (P.map e.inv.op).hom ((P.map e.hom.op).hom x) = x := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
    PresheafOfModules.map_id_apply]

/-- The sections of a presheaf of modules over two isomorphic objects of the site agree, by
restriction along the isomorphism. Stated with everything free, for the reason recorded on
`Stacks.AlgebraicGeometry.ThetaGlobal.map_op_roundtrip`. -/
def sectionsEquivOfSiteIso {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {U V : C} (e : U ≅ V) :
    P.obj (op V) ≃+ P.obj (op U) where
  toFun := (P.map e.hom.op).hom
  invFun := (P.map e.inv.op).hom
  left_inv := map_op_roundtrip P e
  right_inv := map_op_roundtrip P e.symm
  map_add' x y := (P.map e.hom.op).hom.map_add x y

/-- The additive equivalence on sections induced by an isomorphism of presheaves of modules.
Stated with everything free, for the reason recorded on
`Stacks.AlgebraicGeometry.ThetaGlobal.map_op_roundtrip`. -/
def sectionsEquivOfIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) (U : Cᵒᵖ) :
    M.val.obj U ≃+ N.val.obj U where
  toFun := (e.hom.val.app U).hom
  invFun := (e.inv.val.app U).hom
  left_inv x :=
    congrArg (fun φ : M ⟶ M => (φ.val.app U).hom x) e.hom_inv_id
  right_inv x :=
    congrArg (fun φ : N ⟶ N => (φ.val.app U).hom x) e.inv_hom_id
  map_add' x y := (e.hom.val.app U).hom.map_add x y

/-- **The degreewise comparison of the two graded modules of twisted sections**: the degree-`m`
summand of `Stacks.SheafOfModules.sectionModule` at `L = 𝒪(d)`, that is the global sections of
`ℱ ⊗ 𝒪(d)^{⊗ m}`, is the degree-`dm` summand of Tag 03GM's graded module, that is `Γ(X, ℱ(dm))`.

This is `Stacks.AlgebraicGeometry.ThetaGlobal.twistTensorPowerIsoNat` read on sections, followed
by the passage from the terminal open to `⊤`. -/
def twistSectionsEquiv (m : ℕ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projSiteRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projSiteRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projSiteSheaf 𝒮))⟩).obj (F)).obj
        ((Stacks.SheafOfModules.TensorPower.tensorPower (projSiteRing 𝒮) (projSiteSheaf 𝒮)
          (twist 𝒮 (d : ℤ)) (m : ℤ))))).val.obj
        (op (⊤_ (Opens (AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace))) ≃+
      twistSections 𝒮 F (d * m) :=
  (sectionsEquivOfIso (twistTensorPowerIsoNat 𝒮 hcover d F m) _).trans
    (sectionsEquivOfSiteIso (twistSheafOfModules 𝒮 F ((d * m : ℕ) : ℤ)).val
      (topIsoTerminal 𝒮))

/-- **A twisted global section of degree `d m` of Tag 03GM, as a homogeneous element of degree
`m` of the graded section module of Tag 01CV.** This is the degreewise half of the comparison
`⨁_m Γ(X, ℱ(d m)) → ⨁_n Γ(X, ℱ ⊗ 𝒪(d)^{⊗ n})` that Tag 03GM's local bijectivity needs; that the
declaration typechecks is the statement that the source of
`Stacks.AlgebraicGeometry.ThetaGlobal.twistSectionsEquiv` is the degree-`m` summand of
`Stacks.SheafOfModules.sectionModule`, with no spelling left over. -/
def toSectionModule (m : ℕ) :
    twistSections 𝒮 F (d * m) →+
      Stacks.SheafOfModules.sectionModule (projSiteRing 𝒮) (projSiteSheaf 𝒮)
        (twist 𝒮 (d : ℤ)) F :=
  (DirectSum.of _ (m : ℤ)).comp (twistSectionsEquiv 𝒮 hcover d F m).symm.toAddMonoidHom

/-- The image of `Stacks.AlgebraicGeometry.ThetaGlobal.toSectionModule` lies in the degree-`m`
homogeneous piece of the graded section module. -/
theorem toSectionModule_mem (m : ℕ) (t : twistSections 𝒮 F (d * m)) :
    toSectionModule 𝒮 hcover d F m t ∈
      Stacks.SheafOfModules.sectionModuleGrading (projSiteRing 𝒮) (projSiteSheaf 𝒮)
        (twist 𝒮 (d : ℤ)) F (m : ℤ) :=
  ⟨_, rfl⟩

end Stacks.AlgebraicGeometry.ThetaGlobal

end
