module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerContractSnake

/-!
# The degreewise family of the comparison `ℳ̃_T ⟶ h^*ℳ̃` on a chart

Situation 01NN fixes a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`, and property (1)
of [Stacks, Tag 01O7] asserts a canonical isomorphism `ℳ̃_T ≅ h^*ℳ̃` for the morphism `h` a
quadruple classifies. By
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.existsUnique_hom` a morphism out of
`ℳ̃_T` is a family of morphisms out of the degreewise summands `f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` of
[Stacks, Tag 01O6] satisfying the balancing relations. Over an **affine** base the two factors of
the degree-`n` member are both available:

* the left one is `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow`,
  `f^*ℳ_{dn} ⟶ h^*(ℳ(dn)~)`;
* the right one is
  `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso`,
  `h^*(ℳ(dn)~) ⊗ L^{⊗ (-n)} ≅ h^*ℳ̃`.

This file composes them into the family `degreewise` and computes its untwisting.

## The two vocabularies meet with one degree transport

A graded module in Situation 01NN is a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule`, with a **left** action of the
homogeneous pieces of `𝒜`, while [Stacks, Tag 01O6]'s summands are built from a
`SheafOfModules.GradedModule`, with a **right** one.
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationModule` is the reading that crosses
between them and it leaves the homogeneous pieces unchanged, so the only discrepancy left is the
spelling of the degree: a summand of [Stacks, Tag 01O6] carries `ℳ_{n·d}` while the shifted
associated sheaf carries `ℳ(d·n)~`, and addition's commutativity is not definitional. The pullback
of `eqToHom (congrArg ℳ.piece (mul_comm n d))` is the whole bridge.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.degreewise`: **the
  degreewise family of the comparison of property (1) of [Stacks, Tag 01O7] on a chart.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.Intertwines`: **the
  intertwining identity** in one bidegree — that the arrow `f^*ℳ_k ⟶ h^*(ℳ(k)~)` carries the
  action of `𝒜` to the action of `ψ(𝒜)` on the Laurent algebra.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.untwist_degreewise`:
  **the untwisting of the family is the shifted arrow followed by the comparison
  `h^*(ℳ(dn)~) ≅ h^*ℳ̃ ⊗ L^{⊗ n}`** — every tensor power of `L` disappears from it.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.relation_of_intertwines`:
  **the intertwining identity is the balancing relation of [Stacks, Tag 01O6] in that
  bidegree.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.intertwines_of_sections`:
  the intertwining identity is checkable on the pure tensors of global sections.
* `RelativeProjQcohSheaf.ChartDegreewiseFamily.existsUnique_hom_of_intertwines`: **the comparison
  `ℳ̃_T ⟶ h^*ℳ̃` exists and is unique on a chart as soon as the intertwining identity holds in
  every bidegree.**

## One spelling per object, and why

`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso` is produced with its
tensor products spelled by `Stacks.RelativeVeryAmple.tensorModules` and its tensor powers by
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`, whereas the degreewise summands of [Stacks,
Tag 01O6] are built from the monoidal product of [Stacks, Tag 01CA] and the homogeneous pieces of
the Laurent algebra. The two agree by `rfl`
(`Stacks.AlgebraicGeometry.PullbackTwistPower.tensorModules_eq_tensorObj_laurent_piece`), but the
kernel's check of that agreement is expensive, and the budget is **one crossing per
declaration**: a `def` whose declared type is at one spelling and whose body is at the other
compiles in seconds, while an *equation* between two such morphisms — which must cross once for
its statement and once for its proof — runs into `(kernel) deterministic timeout` after three
minutes. This holds even for the equation stating by
`rfl` the very factorisation `degreewise` is *defined* by.

So each of `shiftHom`, `powContract` and `shiftedArrow` is a `def` with the summands' spelling
declared and the other spelling in its body, one crossing apiece, and `contractHom` is assembled
from the first two **inside** this file rather than imported as
`pullbackShiftedContractIso`. That is what lets `untwist_contractHom` be proved at all: the two
factors already carry the right spelling, so the cancellation is
`Stacks.Monoidal.untwist_eq_of_whiskerRight` with a `rfl`, and the kernel is asked for no
comparison of monoidal products. Asserting the same cancellation of
`pullbackShiftedContractIso` directly does not get through.

## What is NOT here

No tag is carried here.

This file belongs to the route to property (1) of [Stacks, Tag 01O7] through the
isomorphism `α : h^*𝒪(d) ≅ L`, and the remarks in this section concern that route only.
The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this file:
on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

On this route the intertwining identity is a hypothesis throughout, so no morphism out of `ℳ̃_T`
is produced unconditionally here; nor is the local isomorphy on the cover of `Y` by the
nonvanishing opens of `ψ`, nor the compatibility with pullbacks.

The two halves of the construction that it needs as inputs are **both
done**, and `Intertwines` is still not proved, for a reason that is not a missing lemma of
either. The three paragraphs below record what is available and then what the obstruction
actually is.

The **module half is complete.**
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul` evaluates the comparison
`ℳ̃ ⊗ 𝒪(a) ⟶ ℳ(a)~` of [Stacks, Tag 01MQ] on a pure tensor of honest sections,
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_apply` gives the pointwise
value of the section a homogeneous element names, and
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_homogeneousScalar` is the
multiplicativity — the global section named by `a · m`, for `a` homogeneous of any natural
degree, is the homogeneous scalar action of `a` on the global section named by `m`. The pointwise
bridge identifying that scalar action with `moduleTwistMap` against the section of `𝒪(i)` that
`a` names is now
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_eq_homogeneousScalar` of
`StacksFrontier/AlgebraicGeometry/ModuleTwistIso/HomogeneousScalar.lean`, and the consequence the
intertwining identity wants of it is `moduleTwistMap_tmul_degreeNToGlobalSections` there: the
comparison carries the pure tensor of the section named by `m` with the section of `𝒪(i)` named
by `a` to the section named by `a · m`.

The **twist half is not an evaluation on sections at all,** and it is also done. What
`shiftHom` needs of the twists is a *morphism* identity, with no section anywhere in its
statement: the multiplicativity of `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` across degrees.
That is `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul` of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean`, in an arbitrary integer
bidegree, with the bidegree `(n, 1)` for an arbitrary integer `n` — the column this file's
induction is run along — available separately as `thetaInt_mul_one`.

**No dictionary between the repository's two integer power families was needed for it.** Earlier
revisions of this note read the two missing inputs as calling for one: the associativity
constraint `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` was stated only for
natural-number exponents, while the other family's
`Stacks.SheafOfModules.TensorPower.monoidalMulIso_assoc` held in every integer degree and the
comparison of the two families is multiplicative only in degree one
(`StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/Recursion.lean`). The restriction was instead
lifted inside the family that had it:
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` is the constraint in an
arbitrary integer tridegree, and the compatibility of the two orders of the inverse law that a
multiplicativity statement crossing the degree zero also needs is derived from it, as
`tensorPowModuleAddIso_snake`.

### `Intertwines` is a compatibility of `α` with `ψ`, and cannot be proved for an arbitrary pair

`Intertwines` takes `α` and `ψ` as **independent** arguments, and nothing relates them:
`Twisting` carries only `app`, `app_mul` and `app_one`, no reference to `φ` or to the pulled-back
twist. Read the identity in bidegree `(n, i)`: the left side meets `α` only through
`shiftHom … α (n + i)`, the right side only through `shiftHom … α n` inside `contractHom`, and
the degree-`i` discrepancy between them is carried by `ψ.app i`, which is the sole occurrence of
`ψ` (`RelationSections.twistLaw`). So the identity *determines* `ψ.app i` from `α` in every
degree `i`, and `∀ α ψ p, Intertwines 𝔐 d φ α ψ p` is therefore not a theorem: it is the
statement that the two data agree.

That agreement is the content of [Stacks, Tag 01N8]: a quadruple's `ψ` determines the chart
`φ = classifyingHom …` together with `α = (classifyingPair …).2`, and
`Stacks.AlgebraicGeometry.PullbackTwistPower.classifyingPullbackShiftedIso` is `pullbackShiftedIso`
specialised to that pair. **A proof of `Intertwines` must either be taken at that pair or carry
the compatibility as a hypothesis**; the general form above is a predicate, not a conjecture,
and `existsUnique_hom_of_intertwines` and `relation_of_intertwines` are correctly stated as
consuming it.

What the identity says once the untwisting is carried out on both of its sides is in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartIntertwineReduction`: writing
`G_n = ChartIntertwineReduction`'s `comparison`, the degree-`n` composite
`f^*ℳ_{nd} ⟶ h^*(ℳ(dn)~) ⟶ h^*ℳ̃ ⊗ L^{⊗ n}`, the identity in bidegree `(n, i)` is

`act ≫ G_{n+i} = (G_n ▷ f^*𝒜_{id}) ≫ ((h^*ℳ̃ ⊗ L^{⊗ n}) ◁ ψ.app i) ≫ laurentShiftAct`,

the `ψ`-equivariance of the family `G`, in which `α` occurs only inside `G` and `ψ` occurs
exactly once; `laurentShiftAct` is computed there, as the associator followed by the
multiplication `L^{⊗ n} ⊗ L^{⊗ i} ⟶ L^{⊗ (n+i)}` of the Laurent algebra whiskered into `h^*ℳ̃`, so
no untwisting and no negative tensor power survive in it. That is `intertwines_iff_compatible` and
`laurentShiftAct_eq` there, and `existsUnique_hom_of_compatible` is
`existsUnique_hom_of_intertwines` consuming the identity in that form. It is an equivalence, not a
discharge.

It also disposes of one reading of the bidegree `(n, 0)` as a cheaper first target. The degree-`i`
discrepancy between the two sides does vanish there — both carry `G_n` — but `Twisting.app_one`
pins `ψ.app 0` only on the image of the unit `𝒪_T ⟶ f^*𝒜_0`, and `𝒜_0` is an arbitrary
quasi-coherent module, not `𝒪_S`. So the bidegree `(n, 0)` identity still asserts that `G_n` is
`𝒜_0`-linear for the action of `𝒜_0` through `ψ.app 0`, which `α` and `ψ` must agree for; it is no
more unconditional than any other bidegree.

### What is still missing even at a compatible pair

An evaluation on global sections of `shiftHom`, i.e. of
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedIso`. Its outer factors are
**not** the problem; each already has a formula on the pullback-unit image of a section:

* `Scheme.Modules.pullbackComp` — `AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_unit` and
  `pullbackSection_comp`, in `StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`;
* `Stacks.RelativeVeryAmple.pullbackTensorModulesIso` — its `hom` is
  `Stacks.PullbackTensorIso.pullbackTensorComparison` by `rfl` (recorded in
  `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPowerPullbackMul.lean`), and that is
  `Stacks.PullbackTensorCoherence.pullbackTensorComparison_pullbackUnit`;
* `Stacks.RelativeVeryAmple.tensorModulesMapIso` —
  `Stacks.SheafOfModules.tensorSections_tensorMapAt` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistSectionRing.lean`, the bifunctor it is the
  `mapIso` of. (It is *not* `⊗ₘ` on the nose; see the note in `TensorPowerPullbackMul`.)

Two factors have no such formula, and they are where the work is.

`restrictedModuleTwistIso` is the one that carries the mathematics, and `pullbackShiftedIso` uses
it **backwards**, so what is wanted is the *inverse* of `moduleTwistMap` on sections. The module
half above pins that inverse down on exactly the sections a homogeneous element names —
`moduleTwistMap` is injective on the ratio locus by
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap` — so this is
bookkeeping across the restriction and pullback functors, not a second mathematical problem.

`pullbackTwistPowIso` is the wall. It is a four-fold composite through
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt`, `Stacks.PowerFamilyBridge.tensorPowerModuleIso`,
`Stacks.TensorPowerPullback.pullbackIntPowIso` and `tensorPowerModuleCongr`, and **not one of
them has a pointwise formula**: every lemma about `ThetaMul.thetaInt` — including
`thetaInt_mul` — is an identity between morphisms. Do not be misled by the section-level theta
results that do exist: `Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_app_natCast` and
`thetaSectionPower_mulBilinear` are about a *different* declaration, `ThetaGlobal.thetaInt` on
`Proj 𝒮` rather than `ThetaMul.thetaInt` on `U_d`.

The family's other factor needs nothing: it is already evaluated, by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow_pullbackUnit`. So is `ψ`,
by `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.sectionHom_apply`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist toProj)
open Stacks.AlgebraicGeometry.PullbackTwistPower
  (powContractIso pullbackShiftedIso untwist_powContractIso)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow (arrow baseHom)
open Stacks.GradedModule (shiftedGrading)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections
  (laurentInvLaw relation_of_untwist_eq rightLaw)
open Stacks.Monoidal (untwist)
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.RingedSpace (structureRingSheaf pullbackFunctor)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] SheafGradedModule.sectionModuleDecomposition

variable {S : Scheme.{u}} [IsAffine S] {A : SheafGradedAlgebra S} (𝔐 : SheafGradedModule A)
  (d : ℕ) {Y : Scheme.{u}}
  (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme)
  {L : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)}
  [Stacks.Ample.IsInvertibleModule Y L]
  [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]

/-- The morphism `h : Y ⟶ Proj Γ(S, 𝒜)` that a morphism `φ : Y ⟶ U_d` into the degree-`d` open
determines, as the composite with the inclusion. -/
abbrev chartHom : Y ⟶ AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)) :=
  toProj (A.grading (⊤ : S.Opens)) φ

/-- **The target `h^*ℳ̃` of the comparison of property (1) of [Stacks, Tag 01O7]**, declared at
the `Stacks.RingedSpace.structureRingSheaf` spelling of the structure sheaf of rings, which is the
one [Stacks, Tag 01O6]'s summands and the monoidal structure of [Stacks, Tag 01CA] are indexed by.

It is a named declaration with that type, rather than a type ascription on the pullback, because
the `AlgebraicGeometry.Scheme.Modules` spelling it is produced at is equal to this one only by
`rfl`: a goal mixing the two is not type-correct at the `implicit` transparency level, so `rw`
refuses to act on it. -/
def pullbackAssociated : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace) :=
  (Scheme.Modules.pullback (chartHom d φ)).obj
    (associatedModuleSheaf (A.grading (⊤ : S.Opens)) (𝔐.sectionModuleGrading (⊤ : S.Opens)))

/-- **The module `h^*(ℳ(d·n)~)`**, declared at the `Stacks.RingedSpace.structureRingSheaf`
spelling for the reason recorded for `pullbackAssociated`, and with the pullback spelled by
`AlgebraicGeometry.Scheme.Modules.pullback` rather than by
`Stacks.RingedSpace.pullbackFunctor`. The two are equal by `rfl`, and this is the spelling
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedIso` produces, so a composite with
that comparison asks the kernel for no comparison of pullback functors; the one crossing between
the two spellings is isolated in `shiftedArrow` below, which is where
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow` enters. -/
def shiftedTarget (n : ℤ) : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace) :=
  (Scheme.Modules.pullback (chartHom d φ)).obj
    (associatedModuleSheaf (A.grading (⊤ : S.Opens))
      (shiftedGrading (𝔐.sectionModuleGrading (⊤ : S.Opens)) ((d : ℤ) * n)))

/-- **The arrow `f^*ℳ_{n·d} ⟶ h^*(ℳ(d·n)~)`**, the left factor of the degree-`n` member of the
comparison, with its source's degree spelled as the summands of [Stacks, Tag 01O6] spell it. The
transport is the pullback of the identification of `ℳ_{n·d}` with `ℳ_{d·n}`; it is the only
discrepancy between the two vocabularies, the left-versus-right action being handled by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationModule`, which leaves the homogeneous
pieces unchanged. -/
def shiftedArrow (n : ℤ) :
    (pullbackFunctor (baseHom A (chartHom d φ)).toLRSHom.toShHom).obj
        ((situationModule 𝔐).piece (n * (d : ℤ))) ⟶
      shiftedTarget 𝔐 d φ n :=
  (pullbackFunctor (baseHom A (chartHom d φ)).toLRSHom.toShHom).map
      (eqToHom (congrArg 𝔐.piece (mul_comm n (d : ℤ)))) ≫
    arrow 𝔐 (chartHom d φ) ((d : ℤ) * n)

/-- **The comparison `h^*(ℳ(dn)~) ≅ h^*ℳ̃ ⊗ L^{⊗ n}`**, declared at the
`Stacks.RingedSpace.structureRingSheaf` spelling of the structure sheaf of rings and with the
tensor product and the tensor power spelled as the degreewise summands of [Stacks, Tag 01O6]
spell them. It is
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedIso`, which produces the same
morphism at another, `rfl`-equal spelling. -/
def shiftHom (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    shiftedTarget 𝔐 d φ n ⟶ pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece n :=
  (pullbackShiftedIso (A.grading (⊤ : S.Opens)) d φ
    (𝔐.sectionModuleGrading (⊤ : S.Opens)) α n).hom

/-- **The contraction `(h^*ℳ̃ ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)} ≅ h^*ℳ̃`** of a tensor power against the
opposite one, at the same spelling. It is
`Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso`. -/
def powContract (n : ℤ) :
    (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece n) ⊗ (laurent L).piece (-n) ⟶
      pullbackAssociated 𝔐 d φ :=
  (powContractIso (pullbackAssociated 𝔐 d φ) n).hom

omit [IsAffine S] in
/-- **Untwisting the contraction is the identity**: it cancels against the insertion of the
opposite tensor power that the untwisting criterion of [Stacks, Tag 01O6]'s balancing relations
uses. This is `Stacks.AlgebraicGeometry.PullbackTwistPower.untwist_powContractIso`. -/
theorem untwist_powContract (n : ℤ) :
    untwist (laurentInvLaw L n) (powContract 𝔐 d φ n) =
      𝟙 (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece n) :=
  untwist_powContractIso (pullbackAssociated 𝔐 d φ) n

/-- **The contraction `h^*(ℳ(dn)~) ⊗ L^{⊗ (-n)} ≅ h^*ℳ̃`**, the right factor of the degree-`n`
member of the comparison: the comparison `shiftHom` whiskered by `L^{⊗ (-n)}`, followed by
`powContract`.

This is `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso` with its two
factors written out — that isomorphism is the same composite, with the whiskering spelled as a
tensor product of an isomorphism with the identity, the two agreeing by
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso_refl_right_hom`. Writing the factors out is
what lets the untwisting be computed here at all: both of them have the summands' spelling
declared, so the composite asks the kernel for no comparison of monoidal products, whereas the
same identity asserted of `pullbackShiftedContractIso` crosses the two spellings twice and
`(kernel) deterministic timeout` is the result. -/
def contractHom (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    shiftedTarget 𝔐 d φ n ⊗ (laurent L).piece (-n) ⟶ pullbackAssociated 𝔐 d φ :=
  MonoidalCategoryStruct.whiskerRight (shiftHom 𝔐 d φ α n) ((laurent L).piece (-n)) ≫
    powContract 𝔐 d φ n

omit [IsAffine S] in
/-- **Untwisting the contraction gives the comparison it was built from.** -/
theorem untwist_contractHom (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    untwist (laurentInvLaw L n) (contractHom 𝔐 d φ α n) = shiftHom 𝔐 d φ α n :=
  Stacks.Monoidal.untwist_eq_of_whiskerRight (laurentInvLaw L n)
    (untwist_powContract 𝔐 d φ n) rfl

/-- **The degreewise family of the comparison `ℳ̃_T ⟶ h^*ℳ̃` of property (1) of [Stacks, Tag
01O7] on a chart.** On the degree-`n` summand `f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` of [Stacks, Tag 01O6] it is
the arrow `f^*ℳ_{nd} ⟶ h^*(ℳ(dn)~)` whiskered by `L^{⊗ (-n)}`, followed by the contraction
`h^*(ℳ(dn)~) ⊗ L^{⊗ (-n)} ≅ h^*ℳ̃`.

This is the family that
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.existsUnique_hom` consumes. Whether it
satisfies the balancing relations is reduced, by `relation_of_intertwines`, to the single
intertwining identity `Intertwines`, which is not proved. -/
def degreewise (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    summand (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) L n ⟶
      pullbackAssociated 𝔐 d φ :=
  MonoidalCategoryStruct.whiskerRight (shiftedArrow 𝔐 d φ n) ((laurent L).piece (-n)) ≫
    contractHom 𝔐 d φ α n

/-- **The untwisting of the degreewise family is the shifted arrow followed by the comparison
`h^*(ℳ(dn)~) ≅ h^*ℳ̃ ⊗ L^{⊗ n}`**: every tensor power of `L` disappears from it.

Untwisting unwhiskers the family's first factor
(`Stacks.Monoidal.untwist_whiskerRight_comp`), and the contraction against `L^{⊗ (-n)}` cancels
against the insertion of `L^{⊗ n}` (`untwist_contractHom`). This is the normalisation that makes
the left-hand side of the intertwining identity `Intertwines` free of tensor powers of `L`. -/
theorem untwist_degreewise (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    untwist (laurentInvLaw L n) (degreewise 𝔐 d φ α n) =
      shiftedArrow 𝔐 d φ n ≫ shiftHom 𝔐 d φ α n :=
  (Stacks.Monoidal.untwist_whiskerRight_comp _ _ _).trans
    (congrArg (shiftedArrow 𝔐 d φ n ≫ ·) (untwist_contractHom 𝔐 d φ α n))

/-! ### The balancing relations -/

/-- **The intertwining identity of property (1) of [Stacks, Tag 01O7] in bidegree `(n, i)`**: the
pulled-back action of `𝒜_{id}` on `ℳ_{nd}`, followed by the untwisted degree-`(n+i)` member of
the family, agrees with the degree-`n` arrow followed by the action of `ψ(𝒜_{id})` on the Laurent
algebra. In words: **the arrow `f^*ℳ_k ⟶ h^*(ℳ(k)~)` intertwines the action of `𝒜` with the
action of `ψ(𝒜)`.**

By `untwist_degreewise` the left-hand side is
`act ≫ (f^*ℳ_{(n+i)d} ⟶ h^*(ℳ((n+i)d)~) ⟶ h^*ℳ̃ ⊗ L^{⊗ (n+i)})`, in which no tensor power of
`L` occurs before the target; and by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.untwist_relRightComp` the
right-hand side is the whole of the `ψ`-side of a balancing relation after its module factor is
split off. Both sides are morphisms `f^*ℳ_{nd} ⊗ f^*𝒜_{id} ⟶ h^*ℳ̃ ⊗ L^{⊗ (n+i)}` out of a
tensor product of two pullbacks of quasi-coherent modules from the affine base `S`, so the
identity is checkable on the pure tensors of global sections by
`Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections`.

It carries the whole content of the balancing relations of [Stacks, Tag 01O6] for this family,
by `relation_of_intertwines`.

**It is a compatibility of `α` with `ψ`, not a property of either.** The two are independent
arguments here, and `α` occurs on the left only in degree `n + i` and on the right only in degree
`n`, the discrepancy being carried by `ψ.app i`; so the identity pins `ψ` down from `α`, and it
holds only for the pair [Stacks, Tag 01N8] attaches to a quadruple. See the module docstring. -/
def Intertwines (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ) :
    Prop :=
  act (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) p.1 p.2 ≫
      untwist (laurentInvLaw L (p.1 + p.2)) (degreewise 𝔐 d φ α (p.1 + p.2)) =
    MonoidalCategoryStruct.whiskerRight (shiftedArrow 𝔐 d φ p.1)
        (AffineTensorGeneral.pullbackSheafMod (baseHom A (chartHom d φ))
          (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2)) ≫
      untwist (laurentInvLaw L (p.1 + p.2))
        (rightLaw L (baseHom A (chartHom d φ)) (d : ℤ) ψ p (contractHom 𝔐 d φ α p.1))

/-- **The intertwining identity is checkable on the pure tensors of global sections.** Its two
sides are morphisms out of `f^*ℳ_{nd} ⊗ f^*𝒜_{id}`, the tensor product of the pullbacks of two
quasi-coherent modules on the affine base `S`, so
`Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections` applies to them
directly: the untwisting has already removed the invertible factor `L^{⊗ (-(n+i))}` that made the
balancing relation itself untestable, an invertible module having in general no nonzero global
section at all. -/
theorem intertwines_of_sections (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ)
    (hyp : ∀ (s : Γ(RelationSections.modulePiece (situationModule 𝔐) (d : ℤ) p.1, ⊤))
        (t : Γ(RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2, ⊤)),
      (act (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) p.1 p.2 ≫
            untwist (laurentInvLaw L (p.1 + p.2))
              (degreewise 𝔐 d φ α (p.1 + p.2))).val.app
          ((opensMap (baseHom A (chartHom d φ)).toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul (baseHom A (chartHom d φ))
            (RelationSections.modulePiece (situationModule 𝔐) (d : ℤ) p.1)
            (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2) s t) =
        (MonoidalCategoryStruct.whiskerRight (shiftedArrow 𝔐 d φ p.1)
              (AffineTensorGeneral.pullbackSheafMod (baseHom A (chartHom d φ))
                (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2)) ≫
            untwist (laurentInvLaw L (p.1 + p.2))
              (rightLaw L (baseHom A (chartHom d φ)) (d : ℤ) ψ p
                (contractHom 𝔐 d φ α p.1))).val.app
          ((opensMap (baseHom A (chartHom d φ)).toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul (baseHom A (chartHom d φ))
            (RelationSections.modulePiece (situationModule 𝔐) (d : ℤ) p.1)
            (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2) s t)) :
    Intertwines 𝔐 d φ α ψ p :=
  have : (RelationSections.modulePiece (situationModule 𝔐) (d : ℤ) p.1).IsQuasicoherent :=
    isQuasicoherent_situationModule_piece 𝔐 (p.1 * (d : ℤ))
  have :
      (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2).IsQuasicoherent :=
    A.isQuasicoherent (p.2 * (d : ℤ))
  AffineTensorGeneral.tensor_hom_ext_of_sections (baseHom A (chartHom d φ))
    (RelationSections.modulePiece (situationModule 𝔐) (d : ℤ) p.1)
    (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2) _ hyp

/-- **The intertwining identity is exactly the balancing relation of [Stacks, Tag 01O6] in that
bidegree.** The degree-`n` member of the family is the shifted arrow whiskered by `L^{⊗ (-n)}`
followed by the contraction, which is the factorisation
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.relation_of_untwist_eq` asks
for. -/
theorem relation_of_intertwines (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ)
    (hint : Intertwines 𝔐 d φ α ψ p) :
    relationLeft (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) L p ≫
        degreewise 𝔐 d φ α (p.1 + p.2) =
      Twisting.relationRight (situationModule 𝔐) ψ p ≫ degreewise 𝔐 d φ α p.1 :=
  relation_of_untwist_eq L (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) ψ p
    (degreewise 𝔐 d φ α) (shiftedArrow 𝔐 d φ p.1) (contractHom 𝔐 d φ α p.1) rfl hint

/-- **The comparison `ℳ̃_T ⟶ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] exists and is unique
on a chart as soon as the intertwining identity holds in every bidegree.** It is the morphism
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.existsUnique_hom` produces from the
degreewise family, whose balancing relations `relation_of_intertwines` supplies.

This is **not** property (1). The intertwining identity is a hypothesis, and that the resulting
morphism is an **isomorphism** — which is local on the cover of `Y` by the nonvanishing opens of
`ψ` — is not asserted. -/
theorem existsUnique_hom_of_intertwines
    (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L)
    (hint : ∀ p : ℤ × ℤ, Intertwines 𝔐 d φ α ψ p) :
    ∃! g : Twisting.associatedSheaf (situationModule 𝔐) ψ ⟶ pullbackAssociated 𝔐 d φ,
      ∀ n : ℤ, Twisting.pureTensor (situationModule 𝔐) ψ n ≫ g = degreewise 𝔐 d φ α n :=
  Twisting.existsUnique_hom (situationModule 𝔐) ψ (pullbackAssociated 𝔐 d φ)
    (degreewise 𝔐 d φ α) fun p => relation_of_intertwines 𝔐 d φ α ψ p (hint p)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily

end
