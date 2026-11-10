module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaInteger
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# The twists and the shifted associated sheaves along a morphism into `Proj`

Let `𝒮` be a graded ring, `d ≥ 0`, and `U_d = ⋃_{f ∈ 𝒮_d} D₊(f) ⊆ Proj 𝒮` the open of Equation
27.12.0.1. A morphism `φ : Y ⟶ U_d` together with an isomorphism `α : φ^*𝒪(d) ≅ L` — the datum a
triple `(d, L, ψ)` of Section 27.12 classifies, by [Stacks, Tag 01N8] — identifies the pullbacks
of the `d`-divisible twists with the integral tensor powers of `L`:

`φ^*𝒪(dn) ≅ L^{⊗ n}` for every `n : ℤ`,

and then, for a graded `𝒮`-module `ℳ`, the pullbacks of the shifted associated sheaves with the
twists of the pullback of `ℳ̃`:

`φ^*(ℳ(dn)~) ≅ φ^*ℳ̃ ⊗ L^{⊗ n}` for every `n : ℤ`.

The first identification was recorded as missing in the implementation notes of
`StacksFrontier.AlgebraicGeometry.MorphismsIntoProj`, which name its two inputs — the comparison
`𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` and the compatibility of the tensor powers with pullback — and
leave the composite unformed. It is formed here, in every integer degree.

## The construction

`φ` factors as `Y ⟶ U_d ⟶ Proj 𝒮`, so `pullbackTwistRestrictIso` contracts the pullback along the
composite into the pullback along `φ` of the restricted twist `𝒪_{U_d}(c)`. On `U_d` the
comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` of [Stacks, Tag 01MU] is
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt`, available in every integer degree; it is stated for
`Stacks.Ample.tensorPowModule` while the pullback comparison
`Stacks.TensorPowerPullback.pullbackIntPowIso` is stated for [Stacks, Tag 01CU]'s own family, and
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` crosses between the two. What remains is to
replace `φ^*𝒪(d)` by `L`, which is `α` applied to all powers at once.

For the shifted sheaves the extra input is the comparison `ℳ̃ ⊗ 𝒪(dn) ⟶ ℳ(dn)~` of [Stacks, Tag
01MQ], an isomorphism on every open contained in the ratio locus of `d`, hence on `U_d`; the
tensor product is commuted past the two pullbacks by [Stacks, Tag 01CD].

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistRestrictIso`: the contraction
  `φ^*𝒪(c) ≅ φ^*(𝒪_{U_d}(c))` of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮`.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.tensorPowerModuleCongr`: the integral tensor
  powers of [Stacks, Tag 01CU] of an invertible module on a scheme depend only on its
  isomorphism class.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistPowIso`: **`φ^*𝒪(dn) ≅ L^{⊗ n}`**, for
  every integer `n`.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.restrictedModuleTwistIso`: the comparison
  `ℳ̃|_{U_d} ⊗ 𝒪_{U_d}(dn) ≅ ℳ(dn)~|_{U_d}` of [Stacks, Tag 01MU] on the degree-`d` open.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedIso`: **`φ^*(ℳ(dn)~) ≅ φ^*ℳ̃ ⊗
  L^{⊗ n}`**, for every integer `n`.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.classifyingPullbackShiftedIso`: the same along the
  morphism a triple of Section 27.12 classifies.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso`: the contraction
  `(𝒩 ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)} ≅ 𝒩` against the opposite tensor power.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso`: **`φ^*(ℳ(dn)~) ⊗
  L^{⊗ (-n)} ≅ φ^*ℳ̃`**, the two preceding isomorphisms composed.

## Main results

* `Stacks.AlgebraicGeometry.PullbackTwistPower.tensorPowerModule_eq_laurent_piece`: the target of
  `pullbackTwistPowIso` is the degree-`n` homogeneous piece of the Laurent algebra of `L`, which
  is the spelling the sheaf of [Stacks, Tag 01O6] is built from. The two are the same object.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.tensorModules_eq_tensorObj_laurent_piece`: the
  source of `pullbackShiftedContractIso` is of the shape of the degreewise summands
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summand` of [Stacks, Tag 01O6], on the nose:
  the tensor product is the monoidal product those are built with and the second factor is the
  degree-`(-n)` piece of the Laurent algebra.

## Implementation notes

The graded ring and its index type are bound in the same universe, `σ : Type u` with `S : Type u`,
because `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` is; the graded module is bound as `M : Type u`
with `τ : Type t`, which is what `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` takes.

Three spellings of the tensor power of an invertible module occur, and all three are needed: the
restricted twists on `U_d` carry `Stacks.Ample.tensorPowModule`, the pullback comparison carries
[Stacks, Tag 01CU]'s `Stacks.SheafOfModules.TensorPower.tensorPower`, and the Laurent algebra of
Section 27.12 is graded by the latter. `Stacks.PowerFamilyBridge.tensorPowerModuleIso` is the
bridge between the first two and `tensorPowerModule_eq_laurent_piece` records that the second and
third agree on the nose.

`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap` is stated for the
restriction functor to an arbitrary open contained in the ratio locus, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` converts it to the pullback along
the open immersion, which is the functor [Stacks, Tag 01CD] commutes with the tensor product.
That is the same conversion `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.isIso_twistMul`
makes for the multiplication maps.

## Not done here

No Stacks tag is carried.

This file belongs to the route to property (1) of [Stacks, Tag 01O7] through the
isomorphism `α : h^*𝒪(d) ≅ L`, and the remarks in this section concern that route only.
The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this
file: on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

What `pullbackShiftedContractIso` supplies is the degree-`n` summand of that property with its
*left* factor still wrong: the summands of [Stacks, Tag 01O6] are `f^*ℳ_{nd} ⊗ L^{⊗ (-n)}`, with
`f` the morphism to the affine base and `ℳ_{nd}` the quasi-coherent module of the degree-`nd`
part, whereas the source below is `φ^*(ℳ(dn)~) ⊗ L^{⊗ (-n)}`. The second factor and the tensor
product agree on the nose, by `tensorModules_eq_tensorObj_laurent_piece`.

The missing left-hand map `f^*ℳ_{nd} ⟶ φ^*(ℳ(nd)~)` is **no longer missing**: it is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow`, recovered by
`Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` from the `Γ(S, 𝒪_S)`-linear map
`ℳ_{nd} ⟶ Γ(Y, φ^*(ℳ(nd)~))` that
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections` prescribes, the linearity
being `Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN_smul_appTop`. What is still
missing after it is the **balancing relations** and the **local isomorphy**. Neither is here; the
relations are reduced, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily`, to the single
intertwining identity `Intertwines`, whose remaining content is an evaluation on global sections
of `pullbackShiftedIso` together with the compatibility of `α` with `ψ` — see the next paragraph.

Nor is the faithful form of [Stacks, Tag 01N7], whose degreewise maps would land in
`Γ(Y, L^{⊗ n})` through `pullbackTwistPowIso`: that needs the multiplicativity of *that*
comparison across degrees, which is not established below. Its main input is, in an arbitrary
integer bidegree: `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul`.

The isomorphisms below are canonical in that they are composites of canonical comparisons, but no
normalization of their values on sections is proved, and that is what the intertwining identity of
property (1) now waits on. Both of the halves that that identity was once said to need are now
available. The module one is
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_degreeNToGlobalSections`, resting on
`moduleTwistMap_tmul` — which evaluates [Stacks, Tag 01MQ]'s `ℳ̃ ⊗ 𝒪(a) ⟶ ℳ(a)~` on a pure tensor
of honest sections — and on
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_homogeneousScalar`, the
multiplicativity of the degreewise global-section map against a homogeneous scalar of any natural
degree; the pointwise bridge between the two is
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_eq_homogeneousScalar`. The twist one
is **not an evaluation on sections**: it is the multiplicativity of
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` across degrees, a morphism identity, and it is
`thetaInt_mul`, in an arbitrary integer bidegree, with the column `(n, 1)` available separately
as `thetaInt_mul_one`.

What remains of the intertwining identity is therefore neither of those halves: it is the
evaluation on global sections of `pullbackShiftedIso` below — for which the factor to compute is
`restrictedModuleTwistIso`, used **backwards**, so what is wanted is the *inverse* of
`moduleTwistMap` on sections, which the module half pins down on the sections a homogeneous
element names — together with the compatibility of `α` with the `ψ` of a quadruple, which
[Stacks, Tag 01N8] supplies and without which the identity is not a theorem at all. The account
is in `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily`. One
normalization that *is* proved, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerContractSnake`, is the cancellation of
`powContractIso` against the insertion of the opposite tensor power that the untwisting criterion
of [Stacks, Tag 01O6]'s balancing relations uses: `untwist_powContractIso` and
`untwist_pullbackShiftedContractIso` there. That is an identity between morphisms, not an
evaluation on sections.

## References

* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01N7](https://stacks.math.columbia.edu/tag/01N7)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist toProj)
open Stacks.AlgebraicGeometry.ProjShifted (moduleTwistMap)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (Triple classifyingHom classifyingPair)
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen (twist)
open Stacks.AlgebraicGeometry.ThetaMul (thetaInt)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.GradedModule (shiftedGrading)
open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso pullbackTensorModulesIso)
open Stacks.SheafOfModules (tensorSheafAssociator tensorLeftFunctorObjUnitIso)
open Stacks.SheafOfModules.TensorPower (coherentMulIso tensorPowerReindex tensorSheafMapIso
  isEquivalence_tensorRightFunctor)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistingSheaf)

universe u t

namespace Stacks.AlgebraicGeometry.PullbackTwistPower

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)
  {Y : Scheme.{u}} (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme)

/-! ### The pullbacks of the `d`-divisible twists -/

/-- **The contraction of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮`.** The twist `𝒪(c)` pulled back
along the composite is the restricted twist `𝒪_{U_d}(c)` pulled back along `φ`. -/
def pullbackTwistRestrictIso (c : ℤ) :
    pullbackTwist 𝒮 φ c ≅ (Scheme.Modules.pullback φ).obj (twist 𝒮 d c) :=
  ((Scheme.Modules.pullbackComp φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app
    (twistingSheaf 𝒮 c)).symm

/-- **The integral tensor powers of [Stacks, Tag 01CU] of an invertible module on a scheme depend
only on its isomorphism class**, in every integer degree. This is
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` with the invertibility class of the
ampleness theory converted to the hypothesis that tensoring on the right is an equivalence, which
is what Tag 01CU's construction is indexed by. -/
def tensorPowerModuleCongr {A B : Y.Modules} [Stacks.Ample.IsInvertibleModule Y A]
    [Stacks.Ample.IsInvertibleModule Y B] (e : A ≅ B) (n : ℤ) :
    tensorPowerModule Y A n ≅ tensorPowerModule Y B n := by
  have hA : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y))⟩).flip.obj
          (A))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A
  have hB : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y))⟩).flip.obj
          (B))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) B
  exact Stacks.SheafOfModules.TensorPower.tensorPowerCongr Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) e n

variable {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- **`φ^*𝒪(dn) ≅ L^{⊗ n}`, in every integer degree.** For a morphism `φ : Y ⟶ U_d` into the
degree-`d` open of `Proj 𝒮` and an isomorphism `α : φ^*𝒪(d) ≅ L` — the datum [Stacks, Tag 01N8]
attaches to a triple `(d, L, ψ)` — the pullback of the twist `𝒪(dn)` is the `n`-th integral
tensor power of `L`.

It is the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` of [Stacks, Tag 01MU] pulled back along
`φ`, read through the compatibility of the tensor powers with pullback and through `α`. -/
def pullbackTwistPowIso (α : pullbackTwist 𝒮 φ (d : ℤ) ≅ L) (n : ℤ) :
    pullbackTwist 𝒮 φ ((d : ℤ) * n) ≅ tensorPowerModule Y L n :=
  pullbackTwistRestrictIso 𝒮 d φ ((d : ℤ) * n) ≪≫
    (Scheme.Modules.pullback φ).mapIso
      ((Stacks.PowerFamilyBridge.tensorPowerModuleIso
        (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) n ≪≫
        thetaInt 𝒮 d n).symm) ≪≫
    Stacks.TensorPowerPullback.pullbackIntPowIso φ.toLRSHom.toShHom (twist 𝒮 d (d : ℤ)) n ≪≫
    tensorPowerModuleCongr ((pullbackTwistRestrictIso 𝒮 d φ (d : ℤ)).symm ≪≫ α) n

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The target of `pullbackTwistPowIso` is the degree-`n` homogeneous piece of the Laurent
algebra of `L`**, the sheaf of graded algebras `⨁_{n ∈ ℤ} L^{⊗ n}` that the map `ψ` of a
quadruple of Section 27.15 takes values in and that the sheaf of [Stacks, Tag 01O6] is built
from. The two objects are the same, so no comparison is needed to feed `pullbackTwistPowIso` to
that construction. -/
theorem tensorPowerModule_eq_laurent_piece
    (hL : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct Y) L) (n : ℤ) :
    tensorPowerModule Y L n =
      (@Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent Y L hL).piece n :=
  rfl

/-- **The contraction `(𝒩 ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)} ≅ 𝒩`.** The two tensor powers multiply to the
zeroth one, which is the structure sheaf, by the coherent multiplication of [Stacks, Tag 01CU] in
the bidegree `(n, -n)`; the associativity and right unit constraints of the tensor product sheaf
do the rest. -/
def powContractIso (N : Y.Modules) (n : ℤ) :
    tensorModules Y (tensorModules Y N (tensorPowerModule Y L n)) (tensorPowerModule Y L (-n))
      ≅ N := by
  have hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L).mpr inferInstance
  have hE : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y))⟩).flip.obj
          (L))).IsEquivalence :=
    isEquivalence_tensorRightFunctor Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L
  exact tensorSheafAssociator Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) N _ _ ≪≫
    tensorSheafMapIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      (Iso.refl N)
      (coherentMulIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L
          n (-n) ≪≫
        tensorPowerReindex Y.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L
          (show n + -n = 0 from add_neg_cancel n)) ≪≫
    tensorLeftFunctorObjUnitIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) N

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **A tensor product with a tensor power of `L` is of the shape of the degreewise summands
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summand` of [Stacks, Tag 01O6]**, on the nose: the
tensor product of `𝒪_Y`-modules is the monoidal product of [Stacks, Tag 01CA] that those summands
are built with, and the tensor power is the homogeneous piece of the Laurent algebra of Section
27.15. Only the left factor of a summand — the pullback of a homogeneous piece of `ℳ` from the
affine base — is a different object. -/
theorem tensorModules_eq_tensorObj_laurent_piece (N : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct Y) L) (n : ℤ) :
    tensorModules Y N (tensorPowerModule Y L n) =
      @MonoidalCategoryStruct.tensorObj _ _
        (@MonoidalCategory.toMonoidalCategoryStruct _ _
          (Stacks.PullbackGradedAlgebra.monoidalCategory Y.toRingedSpace)) N
        ((@Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent Y L hL).piece n) :=
  rfl

/-! ### The pullbacks of the shifted associated sheaves -/

variable {M : Type u} {τ : Type t} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The comparison `ℳ̃ ⊗ 𝒪(dn) ≅ ℳ(dn)~` on the degree-`d` open.** The canonical map of
[Stacks, Tag 01MQ] restricts to an isomorphism on every open contained in the ratio locus of `d`,
by [Stacks, Tag 01MU], and `U_d` is such an open. The restriction of the tensor product is the
tensor product of the restrictions by [Stacks, Tag 01CD], restriction to an open being pullback
along the open immersion. -/
def restrictedModuleTwistIso (n : ℤ) :
    tensorModules (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).obj
          (associatedModuleSheaf 𝒮 𝒨))
        ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).obj
          (twistingSheaf 𝒮 ((d : ℤ) * n))) ≅
      (Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).obj
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((d : ℤ) * n))) :=
  (pullbackTensorModulesIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
      (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 ((d : ℤ) * n))).symm ≪≫
    @asIso _ _ _ _ _ ((NatIso.isIso_map_iff
      (Scheme.Modules.restrictFunctorIsoPullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι)
      (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n))).mp
      (Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap 𝒮 𝒨
        (Stacks.AlgebraicGeometry.ProjDegreeOpenSections.degreeOpen_le_ratioLocus 𝒮 d) n))

/-- **`φ^*(ℳ(dn)~) ≅ φ^*ℳ̃ ⊗ L^{⊗ n}`, in every integer degree.** For a morphism `φ : Y ⟶ U_d`
into the degree-`d` open of `Proj 𝒮`, an isomorphism `α : φ^*𝒪(d) ≅ L`, and a graded
`𝒮`-module `ℳ`, the pullback of the associated sheaf of the shift `ℳ(dn)` is the pullback of
`ℳ̃` twisted by the `n`-th integral tensor power of `L`.

It is `restrictedModuleTwistIso` pulled back along `φ`, with the tensor product commuted past the
pullback by [Stacks, Tag 01CD] and the second factor identified by `pullbackTwistPowIso`. -/
def pullbackShiftedIso (α : pullbackTwist 𝒮 φ (d : ℤ) ≅ L) (n : ℤ) :
    (Scheme.Modules.pullback (toProj 𝒮 φ)).obj
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((d : ℤ) * n))) ≅
      tensorModules Y
        ((Scheme.Modules.pullback (toProj 𝒮 φ)).obj (associatedModuleSheaf 𝒮 𝒨))
        (tensorPowerModule Y L n) :=
  ((Scheme.Modules.pullbackComp φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app
      (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((d : ℤ) * n)))).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso (restrictedModuleTwistIso 𝒮 d 𝒨 n).symm ≪≫
    pullbackTensorModulesIso φ _ _ ≪≫
    tensorModulesMapIso Y
      ((Scheme.Modules.pullbackComp φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app
        (associatedModuleSheaf 𝒮 𝒨))
      ((pullbackTwistRestrictIso 𝒮 d φ ((d : ℤ) * n)).symm ≪≫ pullbackTwistPowIso 𝒮 d φ α n)

/-- **`φ^*(ℳ(dn)~) ⊗ L^{⊗ (-n)} ≅ φ^*ℳ̃`, in every integer degree.** The degree-`n` summand of
property (1) of [Stacks, Tag 01O7], with its left factor read as the pullback of the shifted
associated sheaf rather than as the pullback of the degree-`nd` piece of `ℳ` from the affine
base: `pullbackShiftedIso` followed by the contraction against the opposite tensor power.

The source is of the shape of the degreewise summands of [Stacks, Tag 01O6], by
`tensorModules_eq_tensorObj_laurent_piece`. -/
def pullbackShiftedContractIso (α : pullbackTwist 𝒮 φ (d : ℤ) ≅ L) (n : ℤ) :
    tensorModules Y
        ((Scheme.Modules.pullback (toProj 𝒮 φ)).obj
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((d : ℤ) * n))))
        (tensorPowerModule Y L (-n)) ≅
      (Scheme.Modules.pullback (toProj 𝒮 φ)).obj (associatedModuleSheaf 𝒮 𝒨) :=
  tensorModulesMapIso Y (pullbackShiftedIso 𝒮 d φ 𝒨 α n) (Iso.refl _) ≪≫
    powContractIso _ n

/-- **`h^*(ℳ(dn)~) ≅ h^*ℳ̃ ⊗ L^{⊗ n}` for the morphism `h` a triple classifies.** This is
`pullbackShiftedIso` at the morphism `Y ⟶ U_d` and the isomorphism `α : h^*𝒪(d) ≅ L` that
[Stacks, Tag 01N8] attaches to a triple `(d, L, ψ)` of Section 27.12. -/
def classifyingPullbackShiftedIso (t : Triple 𝒮 Y) (n : ℤ) :
    (Scheme.Modules.pullback t.classifyingMorphism).obj
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((t.deg : ℤ) * n))) ≅
      @tensorModules Y
        ((Scheme.Modules.pullback t.classifyingMorphism).obj (associatedModuleSheaf 𝒮 𝒨))
        (@tensorPowerModule Y t.module t.isInvertible n) :=
  haveI := t.isInvertible
  pullbackShiftedIso 𝒮 t.deg (classifyingHom 𝒮 t.deg_pos t.psi t.generated) 𝒨
    (classifyingPair 𝒮 t.deg_pos t.psi t.generated).2 n

end Stacks.AlgebraicGeometry.PullbackTwistPower

end
