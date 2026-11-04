module

public import StacksFrontier.AlgebraicGeometry.SectionRingVeroneseChart.DegreeOne

/-!
# Stacks Situation 01QH's map, and the second claim of Stacks Tag 01QI

Stacks Situation 28.29.1, Tag 01QH, is: *"Let `X` be a scheme. Let `𝓛` be an ample invertible
sheaf on `X`. Set `S = Γ_*(X, 𝓛)` as a graded ring. Set `Y = Proj(S)`. Let `f : X → Y` be the
canonical morphism of Lemma 28.27.9. It comes equipped with a `ℤ`-graded `𝒪_X`-algebra map
`⨁ f^*𝒪_Y(n) → ⨁ 𝓛^{⊗ n}`."*

Stacks Tag 28.29.2, Tag 01QI, has two claims. The first — that `f` maps `X` into Tag 01MU's open
`W = W_1 ⊆ Y` — is
`Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`. The second is:
*"Moreover, the maps `f^*𝒪_Y(n) → 𝓛^{⊗ n}` are all isomorphisms."*

**This file supplies the map of the Situation, degreewise in every integer degree, and proves the
second claim.** Its multiplicativity in an arbitrary integer bidegree — the other half of the
Situation's claim that the family is a map of graded algebras — is
`Stacks.SectionRingVeroneseChart.twistComparison_mul`, in
`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean`. The map is

`Stacks.SectionRingVeroneseChart.twistComparison`,

the forward map of the composite

`f^*𝒪_Y(n) ≅ (f^*𝒪_Y(1))^{⊗ n} ≅ 𝓛^{⊗ n}`

whose first leg is the pullback of Tag 01MU's comparison on `W₁`
(`Stacks.SectionRingVeroneseChart.pbTwistIsoTensorPow`) and whose second is the `n`-th tensor
power of the degree-one comparison `Stacks.SectionRingVeroneseChart.degreeOneIso`.

## Where the content is

**Not in the invertibility.** Every leg of the composite is an isomorphism, so the second claim of
Tag 01QI is immediate once the map is built; the mathematics is in the map being *the* canonical
one. That is what the degree-one comparison carries:

* `Stacks.SectionRingVeroneseChart.degreeOneIso` is not chosen on a chart. It descends from
  `Stacks.SectionRingVeroneseChart.twistIso`, the second component `α` of the pair that Stacks
  Tag 01N8 proves **unique**, normalised by
  `Stacks.SectionRingVeroneseChart.pair_snd_hom_app_top`: `α` carries the pulled-back degree-`d`
  section of a homogeneous `g ∈ S_d` to the global section `ψ(g)` of `𝓛^{⊗ d}` that `g` is. The
  morphism `f` the pullback is taken along is pinned too, by
  `Stacks.SectionRingVeroneseChart.pair_fst_eq_degreeLift`, to the canonical morphism of Stacks
  Tag 01PZ.
* The descent from degree `d` to degree one, and the propagation to every integer degree, use only
  Tag 01MU's comparison on `W₁`, Tag 01CU's addition law for the tensor powers and Tag 01CD's
  commutation of pullback with the tensor product. Nothing is chosen there either.

Had the comparison instead been *defined* on the ratio charts of `W₁` by sending a trivializing
generator of `𝒪_{W₁}(1)` to a trivializing section of `𝓛`, the second claim of Tag 01QI would
have been true by construction and about nothing. It is not so defined.

## Main definitions

* `Stacks.SectionRingVeroneseChart.twistComparisonIso` — the comparison
  `f^*𝒪_Y(n) ≅ 𝓛^{⊗ n}`, in every integer degree.
* `Stacks.SectionRingVeroneseChart.twistComparison` — **Situation 01QH's map**, degreewise: the
  forward map of `twistComparisonIso`.

## Main results

* `Stacks.SectionRingVeroneseChart.isIso_twistComparison` — **the second claim of Stacks Tag
  01QI**: the maps `f^*𝒪_Y(n) → 𝓛^{⊗ n}` are isomorphisms, for every integer `n`.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)

## What is not done here

**The map is a map of graded algebras, and the multiplicativity is in another file.** Situation
01QH calls its map a `ℤ`-graded `𝒪_X`-algebra map, and the other half of that — multiplicativity
in an arbitrary integer bidegree `(n, m)` — is
`Stacks.SectionRingVeroneseChart.twistComparison_mul`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean`), which cannot live
here because its proof consumes the five legs' bidegree squares and those files import this one.
The graded `𝒪_X`-algebra structure on the source `⨁_{n ∈ ℤ} f^*𝒪_Y(n)` is
`Stacks.SectionRingVeroneseChart.pbTwistMul` there: Tag 01MO's multiplication of the twisting
sheaves pulled back along the canonical morphism and conjugated by Tag 01CD. On the target it is
Tag 01CU's addition law `Stacks.Ample.tensorPowModuleAddIso`. A homomorphism of sheaves of
`ℤ`-graded algebras in this repository — `Stacks.SheafOfModules.GradedAlgebra.Hom`, registered for
Stacks Tag 0FQW — is exactly a degreewise family together with multiplicativity in every bidegree,
so `twistComparison` and `twistComparison_mul` make the family such a homomorphism, and both carry
the `@[stacks 01QH]` registration.

**Unit preservation, the third datum, is in a third file.** It is the extra datum of
`Stacks.SheafOfModules.GradedAlgebra.UnitalHom` over `GradedAlgebra.Hom`, and it is
`Stacks.SectionRingVeroneseChart.pbTwistUnit_twistComparison`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebraUnit.lean`), which also
carries the `@[stacks 01QH]` registration. The three together are the Situation's `ℤ`-graded
`𝒪_X`-algebra map. It is not independent of the above and is proved from it: the degree-zero pieces
of both algebras are `𝒪_X`, both units are forced, and the bidegree `(0, m)` case of
`twistComparison_mul` makes the two candidates agree after tensoring on the right by the invertible
module `f^*𝒪_Y(m)`, by which tensoring is faithful (Stacks Tag 0FFM). The global-sections argument
— that the degree-zero component is multiplication by a global unit which the bidegree `(0, 0)`
case shows idempotent — is not needed.

**The route, and what each leg contributed.** `twistComparisonIso` is a composite of five legs —
the four of `Stacks.SectionRingVeroneseChart.pbTwistIsoTensorPow` and one more
`tensorPowModuleIsoOfIsoInt` — and the bidegree square for it is the five legs' squares pasted:

* *The twist leg on `W₁`, pulled back along the lift.*
  `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul` is the bidegree square for `theta` on `W₁`
  in an arbitrary integer bidegree, and `Stacks.SectionRingVeroneseChart.pullbackTheta_mul`
  transports it along `Scheme.Modules.pullback` by `Stacks.Monoidal.pullback_mul_square`, which is
  Tag 01CD's naturality made into a reusable statement.
* *The pullback leg.*
  `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackTensorPowModuleIntIso_mul`, for arbitrary
  integers and an arbitrary morphism of schemes.
* *The transport leg, which is two of the five legs.*
  `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_mul`, for an arbitrary
  scheme and an arbitrary isomorphism of invertible modules, so it covers both occurrences.
  Deliberately untagged: Tag 01CU is the *definition* of the tensor power and says nothing about
  comparing the powers of two modules.
* *The structural leg `pbTwistIsoGood`.* `Stacks.SectionRingVeroneseChart.pbTwistIsoGood_mul`, in
  the file named above. It is `Stacks.Monoidal.pullbackComp_mul_eqToHom` — the transport along
  `goodLift_comp_ι` pasted with `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackComp_mul`,
  the composition law for pullback for an arbitrary multiplication on the base — read at the
  ascribed multiplication `Stacks.AlgebraicGeometry.TwistTensor.twistMulModules`.

Two mechanical obstacles arise, and they are recorded with their resolutions in the
implementation notes of `StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean`: the multiplication of the twisting
sheaves has to be ascribed at the `Stacks.RelativeVeryAmple.tensorModules` spelling (at `⊗` the
`MonoidalCategoryStruct` instance for the `projStructureRing 𝒮` spelling is not found at all), and
every defeq step has to be isolated into its own `rfl` lemma, the two free-shape movers
`Stacks.Monoidal.square_of_eq_free` and `square_transfer_free` taking those unfoldings as inputs —
pasting at the concrete objects in one `exact` exceeds the heartbeat allowance in `isDefEq` and in
`whnf`.

**The characterising identity of the tensor-inverse uniqueness isomorphism is in the library,
and must not be re-derived.** Both negative halves — `pullbackTensorPowModuleNegSuccIso` and
`tensorPowModuleIsoOfIsoNegSucc` — are built out of
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso`, the uniqueness isomorphism of a
tensor inverse, and without a characterising identity for that isomorphism no arrangement of
`Stacks.AlgebraicGeometry.ThetaMul.square_step` and `Stacks.Monoidal.square_step_left` reaches a
bidegree summing to zero. The identity is
`Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/TensorUnitUniqueInvLaw.lean`):
`(isoOfTensorUnitIso X A A' B e e').hom ▷ B ≫ e'.hom = e.hom`, with
`Stacks.Monoidal.whiskerRight_tensorUnitComparison` the braided-monoidal statement behind it. It
was not free: for the *two-sided* uniqueness isomorphism `Stacks.Monoidal.isoOfTensorInverse` the
analogous identity is `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`;
`isoOfTensorUnitIso` is instead the **braided** construction, through
`Stacks.SheafOfModules.tensorInverseUniqueIso`, and its version of the identity is not a formal
consequence of the symmetric monoidal axioms — in super vector spaces the odd line is invertible
with `β_ L L = -𝟙`, the comparison of that line with itself built this way is `-𝟙`, and the two
sides differ by a sign. The braiding input that excludes the counterexample is
`Stacks.Monoidal.braiding_eval_snake`, whose hypothesis
`[Stacks.GradedSections.HasTrivialSelfBraiding L]` is about the self-braiding of *one* object —
here the common tensor inverse `B` — and leaves the pair unconstrained;
`Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl` discharges it for every invertible sheaf
of modules.

**The squares are also proved at Tag 01CU's own spelling, and reading them here is not possible.**
The two statements at that spelling
(`Stacks.AlgebraicGeometry.PullbackTwistPower.tensorPowerModuleCongr_coherentMulIso`,
`StacksFrontier/AlgebraicGeometry/TwistTensor/PullbackTwistPowerFactors.lean`:204, and
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`,
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerPullbackMultiplication.lean`:138, read at
a morphism of schemes by `Stacks.Algebraization.pullbackTensorPowSchemeIso_eq_pullbackIntPowIso`)
are real, but transporting them to the `Stacks.Ample.tensorPowModule` spelling the legs are written
in needs the multiplicativity of the bridge between the two spellings of the powers, and **no
statement in the repository relates `coherentMulIso` to `tensorPowModuleAddIso`** — searched by
those two constants co-occurring in a statement and by the bridge co-occurring with either
multiplication. `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow` and its scheme-level form
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` compare the two spellings in every integer degree
and everything proved about them is the two recursion equations. So the direct chase was the
shorter route, and it is the one taken.

* *Through Stacks Tag 01NK's `θ`.* `Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta` is
  already a homomorphism **of sheaves of `ℤ`-graded algebras**
  `r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`, for an arbitrary graded ring and
  an arbitrary graded map `ψ` of Tag 01NK. Situation 01QH is its instance at `𝒜 = Γ_*(X, 𝓛)`'s
  grading and `ψ` the identity of the section ring, and there the algebra structure comes for
  free: what has to be supplied is the datum
  `…ProjChartFullGraded.GradedSections` at the section ring, the identity `U(ψ) = X` from
  ampleness, and the identification of `r_{L, ψ}` with the canonical morphism of Stacks Tag 01PZ.
  The declarations here are not a replacement for that and do not subsume it: `theta` is a map
  stated with no ampleness hypothesis, while `twistComparisonIso` is an isomorphism in the ample
  section-ring situation only.

**The diagram half of Stacks Tag 0EKI is still not proved and nothing here is registered for
it.** Both left-hand entries of Tag 0EKG's diagram are relative spectra of the twist *algebras*
(`Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso`,
`puncturedConeRelativeSpecTwistAlgebraIso`), so the clause needs the comparison at the
`Stacks.SheafOfModules.GradedAlgebra` packaging and then as a
`Stacks.RelativeSpec.AlgebraSheaf` map, which `twistComparison_mul` does not supply: it is the
multiplicativity of the degreewise family, not that family bundled as a
`GradedAlgebra.Hom`. The degreewise identification at the tag's own hypotheses is
`Stacks.SectionRingProjIso.twistIsoTensorPow`, deliberately left untagged — a step towards the
diagram clause, not the clause.

**`twistComparisonIso` in degree `d` is not identified with `twistIso`.** See the same note in
`StacksFrontier/AlgebraicGeometry/SectionRingVeroneseChart/DegreeOne.lean`. With
`twistComparison_mul` in hand the obstruction there is no longer the bidegree square; what is missing is
the uniqueness argument that two multiplicative families agreeing in degree one agree in every
degree, which the repository does not carry.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorPowModuleIsoOfIsoInt)

universe u

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

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-! ### The comparison in every integer degree -/

/-- **`f^*𝒪_Y(n) ≅ 𝓛^{⊗ n}`, for every integer `n`.** The pullback of Tag 01MU's comparison on
`W₁`, `pbTwistIsoTensorPow`, followed by the `n`-th integer tensor power of the degree-one
comparison `degreeOneIso`. -/
def twistComparisonIso (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    pbTwist L hL n ≅ tensorPowModule X L n :=
  pbTwistIsoTensorPow L hL n ≪≫
    tensorPowModuleIsoOfIsoInt X (pbTwist L hL 1) L (degreeOneIso L hL) n

/-- **Stacks Situation 01QH's map, in degree `n`**: the component
`f^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}` of the `ℤ`-graded `𝒪_X`-algebra map the Situation equips the canonical
morphism with. It is the forward map of `twistComparisonIso`, whose degree-one value is the
comparison that Stacks Tag 01N8's uniqueness pins. -/
@[stacks 01QH "the Z-graded O_X-algebra map of the Situation, degreewise in every integer degree.
The rest of the Situation's claim is what makes the family a map of graded algebras rather than a
family of maps, and is in two further files: multiplicativity in an arbitrary integer bidegree
(n, m) is Stacks.SectionRingVeroneseChart.twistComparison_mul in
StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean, where the graded
O_X-algebra structure on the source is pbTwistMul, and unit preservation -- the extra datum of
GradedAlgebra.UnitalHom -- is Stacks.SectionRingVeroneseChart.pbTwistUnit_twistComparison in
StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebraUnit.lean. The three together
are the Situation's map. See the 'What is not done here' section above"]
def twistComparison (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    pbTwist L hL n ⟶ tensorPowModule X L n :=
  (twistComparisonIso L hL n).hom

/-- **The second claim of Stacks Tag 01QI: the maps `f^*𝒪_Y(n) → 𝓛^{⊗ n}` are all
isomorphisms.** -/
@[stacks 01QI "the second claim: the maps f^*O_Y(n) -> L^{(x)n} are all isomorphisms, in every
integer degree. The first claim, that the canonical morphism maps X into W_1, is
Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible"]
theorem isIso_twistComparison (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    IsIso (twistComparison L hL n) :=
  inferInstanceAs (IsIso (twistComparisonIso L hL n).hom)

/-- The comparison in a nonnegative degree, with its target at the iterated tensor product
`Stacks.TensorPowers.natTensorPow` rather than the integer power: in a nonnegative degree the two
are the same object, and this is the spelling Stacks Tag 01N8's comparison and the section ring
are indexed by. -/
def twistComparisonIsoNat (hL : Stacks.Ample.IsAmple X L) (n : ℕ) :
    pbTwist L hL (n : ℤ) ≅ natTensorPow L n :=
  twistComparisonIso L hL (n : ℤ)

end Monoidal

end Stacks.SectionRingVeroneseChart

end
