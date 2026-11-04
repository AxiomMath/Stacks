module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FirstOrderExtension

/-!
# From first-order crystal data to modules with an integrable connection

Let `(D, J, γ)` be a divided power ring over a base ring `A`, let `Ω` be a `D`-module and let
`d : D → Ω` be a divided power derivation of `D` over `A`.  In the situation of [Stacks, Tag
07JG] — Situation 07MD together with a surjective polynomial presentation `A[x_i] → C` — these
are the ring `D` of 07J8, the module `Ω_D` of 07J9 and the derivation of 07JA.

The *first-order universal thickening* of `(D, J, γ)` is the trivial square-zero extension
`D ⊕ Ω` with the divided power structure `γ'_{k+1}(f, ω) = (γ_{k+1} f, γ_k f · ω)` on the ideal
`J ⊕ Ω`, the ring-level form of the thickening `(U, T', δ')` of [Stacks, Tag 07J2].  It carries
two divided power sections of its projection to `D`,

`p₀ : f ↦ (f, 0)`  and  `p₁ : f ↦ (f, d f)`,

whose difference is `d`.  A crystal in `𝒪_{X/S}`-modules identifies the pullbacks of a module
`M` along `p₀` and along `p₁`; `Crystalline.FirstOrderComparison` is that identification, read
as a map `ε : M → (D ⊕ Ω) ⊗_{D, p₀} M` which is additive, reduces to the identity modulo `Ω`,
and is semilinear for `p₁`.  The connection of [Stacks, Tag 07JG] is the differential component
`∇ = π_Ω ∘ ε` of the comparison map, and its Leibniz rule is *derived* from semilinearity:
there is no second place where the Leibniz rule is assumed.

## Main definitions

* `Crystalline.firstOrderDividedPowers` — the divided power structure on the ideal `J ⊕ Ω` of
  the first-order thickening `D ⊕ Ω`.
* `Crystalline.firstOrderP₀`, `Crystalline.firstOrderP₁` — the two sections `D → D ⊕ Ω`.
* `Crystalline.firstOrderReduction`, `Crystalline.firstOrderDifferentialPart` — the two
  components `M` and `Ω ⊗_D M` of a section over the first-order thickening.
* `Crystalline.FirstOrderComparison` — the first-order comparison datum of a crystal in
  modules, and `Crystalline.FirstOrderComparison.connection` the connection it determines.
* `Crystalline.FirstOrderComparison.completedConnection` — the same connection read in the
  completed tensor product `M ⊗̂_D Ω`, that is item (07JC) of Tag 07JG.
* `Crystalline.FirstOrderCrystal` and `Crystalline.FirstOrderCrystalHom` — the source category
  of the functor below, and `Crystalline.structureComparison` the comparison datum of the
  structure sheaf, which witnesses that the notion is not vacuous.

## Main results

* `Crystalline.FirstOrderComparison.connection_leibniz` — **the Leibniz rule**, derived from
  semilinearity of the comparison map for `p₁`.
* `Crystalline.firstOrderP₀_isDPMorphism`, `Crystalline.firstOrderP₁_isDPMorphism` — both
  sections are compatible with the divided powers on `J` and `J ⊕ Ω`; for `p₁` this is the
  divided power chain rule obeyed by a divided power derivation.
* `Crystalline.firstOrderP₁_sub_P₀` — the difference of the two sections is `d`.
* `Crystalline.structureComparison_connection` — the connection of the comparison datum of the
  structure sheaf is `d` itself.
* `Crystalline.connection_naturality` — a map compatible with two comparison maps is
  horizontal for the connections they determine.
* `Crystalline.firstOrderCrystalsToPairs` — the functor to the pairs `(M, ∇)` satisfying items
  (07JB), (07JC), (07JD) and (07JE), which are `Crystalline.Pair`.  It proves item (07JC); the
  version of it whose source proves the other three is `Crystalline.taylorCrystalsToPairs`.

## What is and is not proved

Tag 07JG states a functor whose source is the crystals in quasi-coherent `𝒪_{X/S}`-modules on
`Cris(X/S)`; that functor is `Crystalline.GlobalCrystallineSituation.SmallSite.crystalPairFunctor`,
which carries the tag.  The source of `Crystalline.firstOrderCrystalsToPairs` is instead the
first-order comparison data over `D`.  Three things stand between the two sources and are **not**
proved here.

* The passage from Situation 07MD to a global crystalline situation 07MF, which is
  [Stacks, Tag 07JN].  The completed envelope is the section ring of no object of `Cris(X/S)`,
  its divided power ideal not being locally nilpotent, so the identification is with a *system*
  of objects: the levels are `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`,
  their section rings are `D(n)/(p)^{N + e}` by `...SmallSite.wholeSpaceSystemLevelRingEquiv` and
  `D(n)` is their inverse limit by `...SmallSite.envelopeLevelRingLimitEquiv`.  The cohomology
  comparison of [Stacks, Tag 07JN] is
  `...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison`; this file does not
  use it.
* The identification of the *sections* of `SheafOfModules.pullback` with a base change.  A
  crystal on `Cris(X/S)` determines the geometric first-order comparison datum — the isomorphism
  `p₀^* F_T ≅ p₁^* F_T` of sheaves of `𝒪_{T'}`-modules obtained by evaluating it at the
  thickening of 07J2 and reading the comparison maps of 07IQ at the two projections, which is
  `Crystalline.GlobalCrystallineSituation.SmallSite.firstOrderComparison`, functorial in the
  crystal and the identity on the diagonal.  Turning that isomorphism into the map
  `M → (D ⊕ Ω) ⊗_D M` which `Crystalline.FirstOrderComparison` asks for is exactly the datum
  `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`: the canonical map
  `(D ⊕ Ω) ⊗_D M → Γ(T', F_{T'})` is `...GlobalCrystallineSituation.diffAction`, which carries no
  hypothesis, and the datum is its inverse.  For the pullback of *presheaves* of modules the
  sections are a base change: `Stacks.NoncommChangeOfRings.Presheaf.objIsoOfIsIso` for a change
  of rings on a fixed site, which is the shape `p₀` and `p₁` have — `T` and `T'` have the same
  underlying space and both projections have identity base — and
  `Stacks.PullbackEquivalence.pullbackObjIsoBaseChange` for a fully faithful functor of sites,
  with no hypothesis on the module.  What those consume is invertibility of the
  *presheaf-level* comparison map of 07IQ, which is
  `Crystalline.GlobalCrystallineSituation.IsCrystal`; the crystal condition of this tag is the
  *sheaf-level* `...SmallSite.IsSheafCrystal`, and
  `Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal` holds with no converse.
  So the open step is the sheafification unit of `W ↦ 𝒪_{T'}(W) ⊗_{𝒪_T(W)} F_T(W)`, which is
  where the quasi-coherence clause of the next item enters.
* The quasi-coherence clause of the source of the tag.  Tag 07JG quantifies over crystals in
  *quasi-coherent* `𝒪_{X/S}`-modules; nothing below or in the geometric construction uses
  quasi-coherence.  The category it cuts out is
  `Crystalline.GlobalCrystallineSituation.SmallSite.QuasiCoherentCrystal`, and what
  quasi-coherence gives on the ambient schemes, a global presentation of `F_T` over every object
  of a localised site with affine base, is
  `...SmallSite.hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine`; neither
  is used in the item above.

The first-order thickening of 07J2 is an *object of* `CRIS(X/S)` and of `Cris(X/S)`, as
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningObject` and
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysObject`, with the three morphisms
of the diagram and the relations `p₀ ∘ i = p₁ ∘ i = id`.

Of the four items of Tag 07JG, only item (07JC) — the connection and its Leibniz rule — is
proved *in this file* from the comparison datum.  Items (07JB), (07JD) and (07JE), and the
existence of coordinate operators that keeps the last two from being vacuous, are the four
fields `isPAdicallyComplete`, `isIntegrable`, `isTopologicallyQuasiNilpotent` and
`hasCoordinateOperators` of `Crystalline.FirstOrderCrystal`, and nothing here derives them.

They are derived from the data the source's own proof produces: `Crystalline.TaylorCrystal`
replaces the four fields by the tower of levels with `M = lim_e M_e`, the annihilation
`p^{N+e} M_e = 0`, and the composite coordinate operators of the expansions of `c` over `D(1)` and
`D(2)`, and `Crystalline.taylorCrystalsToPairs` is `Crystalline.forgetToFirstOrderCrystal`
followed by the functor below.  `Crystalline.firstOrderCrystalsToPairs` is what the two algebraic
functors have in common and is where item (07JC) lives.

## Implementation notes

The first-order thickening is `Crystalline.firstOrderExtension`, the trivial square-zero
extension of Mathlib, and its divided power structure is `Crystalline.squareZeroDividedPowers`
applied to the additive presentation `Crystalline.firstOrderEquiv` of its sections as pairs;
nothing about divided powers is built again here.  The two sections are recognized as divided
power morphisms through `Crystalline.isDPMorphism_squareZero_of_graph`, which asks exactly for
the divided power chain rule `d (γ_{k+1} f) = γ_k f · d f` that
`Crystalline.DividedPowerDerivation.map_dpow` supplies.

The comparison map takes values in `(D ⊕ Ω) ⊗[D] M` with `D ⊕ Ω` in the *left* factor, because
that is the side on which Mathlib's tensor product carries a module structure over the larger
ring, which is what semilinearity for `p₁` needs.  The connection of `Crystalline.Pair` takes
values in the completion of `M ⊗[D] Ω`, so the two factors are exchanged once, in
`Crystalline.FirstOrderComparison.completedConnection`.

Semilinearity is stated for `p₁` against the `p₀`-structure on the target rather than as an
isomorphism of two base changes, which would need two different `Algebra D (D ⊕ Ω)` instances
on one type.  The two formulations carry the same information: a `p₁`-semilinear map reducing
to the identity is the same thing as a comparison isomorphism `p₀^* M ≅ p₁^* M` that is the
identity modulo `Ω`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07JA](https://stacks.math.columbia.edu/tag/07JA)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w uA uI uM

namespace Crystalline

section FirstOrderThickening

variable (A : Type uA) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D)
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega]
  [IsCentralScalar D Omega]

/-- The sections of `D ⊕ Ω` read as pairs. -/
public def firstOrderEquiv : firstOrderExtension D Omega ≃+ (D × Omega) where
  toFun x := (x.fst, x.snd)
  invFun y := (y.1, y.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A section of `D ⊕ Ω` read as a pair is its two components. -/
@[simp] public theorem firstOrderEquiv_apply (x : firstOrderExtension D Omega) :
    firstOrderEquiv D Omega x = (x.fst, x.snd) := rfl

/-- The image of `a ∈ D` in `D ⊕ Ω` reads as the pair `(a, 0)`. -/
public theorem firstOrderEquiv_inl (a : D) :
    firstOrderEquiv D Omega (algebraMap D (firstOrderExtension D Omega) a) = (a, 0) := rfl

/-- Multiplication in `D ⊕ Ω`, read on pairs: `(a, ω) (a', ω') = (a a', a ω' + a' ω)`. -/
public theorem firstOrderEquiv_mul (b b' : firstOrderExtension D Omega) :
    firstOrderEquiv D Omega (b * b') =
      ((firstOrderEquiv D Omega b).1 * (firstOrderEquiv D Omega b').1,
        (firstOrderEquiv D Omega b).1 • (firstOrderEquiv D Omega b').2 +
          (firstOrderEquiv D Omega b').1 • (firstOrderEquiv D Omega b).2) := by
  refine Prod.ext (TrivSqZeroExt.fst_mul b b') ?_
  show (b * b').snd = b.fst • b'.snd + b'.fst • b.snd
  rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul]

/-- A section of `D ⊕ Ω` lies in the ideal `J ⊕ Ω` exactly when its first component lies
in `J`. -/
public theorem mem_firstOrderExtensionIdeal_iff (b : firstOrderExtension D Omega) :
    b ∈ firstOrderExtensionIdeal D Omega ↔ (firstOrderEquiv D Omega b).1 ∈ D.ideal := Iff.rfl

/-- The divided power structure on the ideal `J ⊕ Ω`. -/
public noncomputable def firstOrderDividedPowers :
    DividedPowers (firstOrderExtensionIdeal D Omega) :=
  squareZeroDividedPowers D.dividedPowers (firstOrderEquiv D Omega)
    (firstOrderExtensionIdeal D Omega) (algebraMap D (firstOrderExtension D Omega))
    (firstOrderEquiv_inl D Omega) (firstOrderEquiv_mul D Omega)
    (mem_firstOrderExtensionIdeal_iff D Omega)

/-- **The map `p₀ : D → D ⊕ Ω`**, the inclusion `f ↦ (f, 0)`. -/
public noncomputable abbrev firstOrderP₀ : D →+* firstOrderExtension D Omega :=
  algebraMap D (firstOrderExtension D Omega)

/-- A ring map `D → D ⊕ Ω` of the form `a ↦ (a, φ a)`, with `φ` obeying the divided power chain
rule, is a divided power morphism. -/
private theorem firstOrder_isDPMorphism_of_graph (f : D →+* firstOrderExtension D Omega)
    (phi : D → Omega) (hf : ∀ a : D, firstOrderEquiv D Omega (f a) = (a, phi a))
    (hphi : ∀ (k : ℕ), ∀ a ∈ D.ideal,
      phi (D.dividedPowers.dpow (k + 1) a) = D.dividedPowers.dpow k a • phi a) :
    DividedPowers.IsDPMorphism D.dividedPowers (firstOrderDividedPowers D Omega) f :=
  isDPMorphism_squareZero_of_graph D.dividedPowers (firstOrderEquiv D Omega)
    (firstOrderExtensionIdeal D Omega) (algebraMap D (firstOrderExtension D Omega))
    (firstOrderEquiv_inl D Omega) (firstOrderEquiv_mul D Omega)
    (mem_firstOrderExtensionIdeal_iff D Omega) f phi hf hphi

/-- `p₀` is a divided power morphism from `(D, J, γ)` to `(D ⊕ Ω, J ⊕ Ω, γ')`. -/
public theorem firstOrderP₀_isDPMorphism :
    DividedPowers.IsDPMorphism D.dividedPowers (firstOrderDividedPowers D Omega)
      (firstOrderP₀ D Omega) :=
  firstOrder_isDPMorphism_of_graph D Omega _ (fun _ ↦ 0) (fun _ ↦ rfl)
    (fun _ _ _ ↦ (smul_zero _).symm)

variable (d : DividedPowerDerivation A D g Omega)

/-- **The map `p₁ : D → D ⊕ Ω`**, the inclusion shifted by the divided power derivation:
`f ↦ (f, d f)`. -/
public noncomputable def firstOrderP₁ : D →+* firstOrderExtension D Omega where
  toFun x := TrivSqZeroExt.inl x + TrivSqZeroExt.inr (d x)
  map_one' :=
    have h : d (1 : (D : Type u)) = 0 := by
      have h1 := d.map_ringHom 1
      rwa [map_one] at h1
    TrivSqZeroExt.ext (by simp) (by simp [h])
  map_mul' x y :=
    TrivSqZeroExt.ext (by simp) (by
      simp [TrivSqZeroExt.snd_mul, op_smul_eq_smul, d.leibniz x y])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (by simp [d.map_add x y])

/-- The first component of `p₁ x` is `x`. -/
@[simp] public theorem firstOrderP₁_fst (x : D) :
    (firstOrderP₁ A D g Omega d x).fst = x := by simp [firstOrderP₁]

/-- The second component of `p₁ x` is `d x`. -/
@[simp] public theorem firstOrderP₁_snd (x : D) :
    (firstOrderP₁ A D g Omega d x).snd = d x := by simp [firstOrderP₁]

/-- `p₁` is a divided power morphism, because a divided power derivation obeys the divided
power chain rule. -/
public theorem firstOrderP₁_isDPMorphism :
    DividedPowers.IsDPMorphism D.dividedPowers (firstOrderDividedPowers D Omega)
      (firstOrderP₁ A D g Omega d) :=
  firstOrder_isDPMorphism_of_graph D Omega _ (fun x ↦ d x) (fun _ ↦ by simp)
    (fun k a ha ↦ d.map_dpow (k + 1) k.succ_pos a ha)

/-- The difference of the two maps `D → D ⊕ Ω` is the divided power derivation, included as
the square-zero summand. -/
public theorem firstOrderP₁_sub_P₀ (x : D) :
    firstOrderP₁ A D g Omega d x - firstOrderP₀ D Omega x =
      (TrivSqZeroExt.inr (d x) : firstOrderExtension D Omega) :=
  TrivSqZeroExt.ext (by simp [TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])

/-! ### The two components of a section over the first-order thickening -/

variable (M : Type w) [AddCommGroup M] [Module D M]

/-- The reduction `(D ⊕ Ω) ⊗_D M → M` of a section over the first-order thickening, obtained
from the projection `D ⊕ Ω → D`. -/
public noncomputable def firstOrderReduction :
    (firstOrderExtension D Omega ⊗[D] M) →ₗ[D] M :=
  (TensorProduct.lid D M).toLinearMap ∘ₗ
    LinearMap.rTensor M (TrivSqZeroExt.fstHom D D Omega).toLinearMap

/-- The differential component `(D ⊕ Ω) ⊗_D M → Ω ⊗_D M` of a section over the first-order
thickening, obtained from the projection `D ⊕ Ω → Ω` onto the square-zero summand. -/
public noncomputable def firstOrderDifferentialPart :
    (firstOrderExtension D Omega ⊗[D] M) →ₗ[D] (Omega ⊗[D] M) :=
  LinearMap.rTensor M (TrivSqZeroExt.sndHom D Omega)

/-- The reduction sends `a ⊗ m` to `a.fst • m`. -/
@[simp] public theorem firstOrderReduction_tmul (a : firstOrderExtension D Omega) (m : M) :
    firstOrderReduction D Omega M (a ⊗ₜ[D] m) = a.fst • m := by
  simp [firstOrderReduction]

/-- The differential component sends `a ⊗ m` to `a.snd ⊗ m`. -/
@[simp] public theorem firstOrderDifferentialPart_tmul (a : firstOrderExtension D Omega)
    (m : M) :
    firstOrderDifferentialPart D Omega M (a ⊗ₜ[D] m) = a.snd ⊗ₜ[D] m := by
  simp [firstOrderDifferentialPart]

/-- **The key identity behind the Leibniz rule.**  Multiplying a section over the first-order
thickening by `p₁ f = (f, d f)` multiplies its differential component by `f` and adds `d f`
tensored with its reduction. -/
public theorem firstOrderDifferentialPart_smul_P₁ (f : D)
    (z : firstOrderExtension D Omega ⊗[D] M) :
    firstOrderDifferentialPart D Omega M (firstOrderP₁ A D g Omega d f • z) =
      f • firstOrderDifferentialPart D Omega M z +
        d f ⊗ₜ[D] firstOrderReduction D Omega M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [TensorProduct.smul_tmul', firstOrderDifferentialPart_tmul,
        firstOrderDifferentialPart_tmul, firstOrderReduction_tmul, smul_eq_mul]
      have h : (firstOrderP₁ A D g Omega d f * a).snd = f • a.snd + a.fst • d f := by
        simp [TrivSqZeroExt.snd_mul, op_smul_eq_smul]
      rw [h, TensorProduct.add_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        TensorProduct.smul_tmul]
      exact congrArg (fun z ↦ a.snd ⊗ₜ[D] (f • m) + z) (TensorProduct.smul_tmul' _ _ _)
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, map_add, hx, hy, smul_add, TensorProduct.tmul_add]
      abel

variable (N : Type w) [AddCommGroup N] [Module D N]

/-- Taking the differential component commutes with a `D`-linear map of the module. -/
public theorem firstOrderDifferentialPart_lTensor (phi : M →ₗ[D] N)
    (z : firstOrderExtension D Omega ⊗[D] M) :
    firstOrderDifferentialPart D Omega N
        (LinearMap.lTensor (firstOrderExtension D Omega) phi z) =
      LinearMap.lTensor Omega phi (firstOrderDifferentialPart D Omega M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- Exchanging the two factors of the tensor product commutes with a `D`-linear map of the
module. -/
public theorem comm_lTensor (phi : M →ₗ[D] N) (z : Omega ⊗[D] M) :
    TensorProduct.comm D Omega N (LinearMap.lTensor Omega phi z) =
      TensorProduct.map phi (LinearMap.id (R := D) (M := Omega))
        (TensorProduct.comm D Omega M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-! ### The first-order comparison datum of a crystal -/

/-- **The first-order comparison datum carried by a crystal in modules.**  For a `D`-module `M`,
this is the comparison map of the crystal along the two divided power sections `p₀, p₁` of the
first-order thickening `D ⊕ Ω` of Tag 07J2, written as a map

`ε : M → (D ⊕ Ω) ⊗_{D, p₀} M`

which is additive, reduces to the identity modulo `Ω`, and is semilinear for `p₁`, that is
`ε (f m) = p₁ f · ε m`.  Semilinearity for `p₁` on the source and the `p₀`-structure on the
target is what it means for the comparison to identify the two pullbacks of `M`; it is the only
input to the Leibniz rule below. -/
public structure FirstOrderComparison (M : Type w) [AddCommGroup M] [Module D M] where
  /-- The underlying comparison map. -/
  toFun : M → firstOrderExtension D Omega ⊗[D] M
  /-- The comparison map is additive. -/
  map_add' : ∀ m n : M, toFun (m + n) = toFun m + toFun n
  /-- The comparison map reduces to the identity modulo the square-zero summand `Ω`. -/
  reduction' : ∀ m : M, firstOrderReduction D Omega M (toFun m) = m
  /-- The comparison map is semilinear for the second divided power section `p₁`. -/
  semilinear' : ∀ (f : D) (m : M),
    toFun (f • m) = firstOrderP₁ A D g Omega d f • toFun m

namespace FirstOrderComparison

variable {A D g Omega d} {M}

/-- A comparison datum coerces to its underlying map. -/
public instance : CoeFun (FirstOrderComparison A D g Omega d M)
    (fun _ ↦ M → firstOrderExtension D Omega ⊗[D] M) where
  coe c := c.toFun

/-- The comparison map is additive. -/
public theorem map_add (c : FirstOrderComparison A D g Omega d M) (m n : M) :
    c (m + n) = c m + c n := c.map_add' m n

/-- The comparison map reduces to the identity modulo `Ω`. -/
@[simp] public theorem reduction (c : FirstOrderComparison A D g Omega d M) (m : M) :
    firstOrderReduction D Omega M (c m) = m := c.reduction' m

/-- The comparison map is semilinear for `p₁`. -/
public theorem semilinear (c : FirstOrderComparison A D g Omega d M) (f : D) (m : M) :
    c (f • m) = firstOrderP₁ A D g Omega d f • c m := c.semilinear' f m

/-- **The connection of a first-order comparison datum**, before completion: the differential
component `∇ m = π_Ω (ε m)` of the comparison map. -/
public noncomputable def connection (c : FirstOrderComparison A D g Omega d M) :
    M → Omega ⊗[D] M :=
  fun m ↦ firstOrderDifferentialPart D Omega M (c m)

/-- The connection of a comparison datum is additive. -/
public theorem connection_add (c : FirstOrderComparison A D g Omega d M) (m n : M) :
    c.connection (m + n) = c.connection m + c.connection n := by
  simp only [connection, c.map_add m n]
  exact (firstOrderDifferentialPart D Omega M).map_add _ _

/-- **The Leibniz rule, derived from the comparison datum.**  This is item (07JC) of Tag 07JG
for the uncompleted tensor product: semilinearity of the comparison map for `p₁` forces
`∇ (f m) = f ∇ m + d f ⊗ m`. -/
public theorem connection_leibniz (c : FirstOrderComparison A D g Omega d M) (f : D) (m : M) :
    c.connection (f • m) = f • c.connection m + d f ⊗ₜ[D] m := by
  rw [connection, c.semilinear f m, firstOrderDifferentialPart_smul_P₁, c.reduction m]
  rfl

end FirstOrderComparison

/-- **The comparison datum of the structure sheaf.**  On `M = D` the comparison map is `p₁`
itself: a section pulled back along `p₁` is the section shifted by its differential.  This is
the one crystal whose connection is known outright, namely `𝒪_{X/S}` with `∇ = d`. -/
public noncomputable def structureComparison :
    FirstOrderComparison A D g Omega d (D : Type u) where
  toFun x := firstOrderP₁ A D g Omega d x ⊗ₜ[D] (1 : D)
  map_add' x y := by rw [map_add, TensorProduct.add_tmul]
  reduction' x := by
    rw [firstOrderReduction_tmul, firstOrderP₁_fst, smul_eq_mul, mul_one]
  semilinear' f x := by
    rw [smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]

/-- The connection of the comparison datum of the structure sheaf is the divided power
derivation itself, so the construction below is not vacuous. -/
public theorem structureComparison_connection (x : D) :
    (structureComparison A D g Omega d).connection x = d x ⊗ₜ[D] (1 : D) := by
  rw [FirstOrderComparison.connection]
  exact (firstOrderDifferentialPart_tmul D Omega (D : Type u)
    (firstOrderP₁ A D g Omega d x) 1).trans (by rw [firstOrderP₁_snd])

/-! ### The completed connection, and the four items of Tag 07JG -/

/-- The divided power derivation read as a bare map `D → Ω`, which is the form in which
`Crystalline.CompletedConnection` and `Crystalline.Pair` take it. -/
public noncomputable abbrev derivationFun : D → Omega := fun x ↦ d x

variable (p : ℕ)

namespace FirstOrderComparison

variable {A D g Omega d} {M}

/-- **Item (07JC) of Tag 07JG.**  The connection of a first-order comparison datum, read in the
completed tensor product `M ⊗̂_D Ω`: the differential component of the comparison map, followed
by the exchange of the two factors and the canonical map to the `p`-adic completion.  The
Leibniz rule is `Crystalline.FirstOrderComparison.connection_leibniz`. -/
public noncomputable def completedConnection (p : ℕ)
    (c : FirstOrderComparison A D g Omega d M) :
    CompletedConnection p D Omega (derivationFun A D g Omega d) M where
  toFun m := toCompletedTensor p D Omega M (TensorProduct.comm D Omega M (c.connection m))
  map_add' m n := by
    rw [c.connection_add m n, _root_.map_add, _root_.map_add]
  leibniz' f m := by
    rw [c.connection_leibniz f m, _root_.map_add, _root_.map_smul, _root_.map_add,
      _root_.map_smul]
    simp [TensorProduct.comm_tmul]

/-- The completed connection is the image of the connection in the completed tensor product,
after exchanging the two factors. -/
@[simp] public theorem completedConnection_apply (p : ℕ)
    (c : FirstOrderComparison A D g Omega d M) (m : M) :
    c.completedConnection p m =
      toCompletedTensor p D Omega M (TensorProduct.comm D Omega M (c.connection m)) := rfl

end FirstOrderComparison

/-! ### The source category: first-order crystal data with the three remaining items -/

variable {ι : Type uI} (dx : ι → Omega)

/-- **The source of the functor of Tag 07JG, in the affine algebraic form of this file.**  A
`D`-module together with the first-order comparison datum of a crystal, and with the three items
of Tag 07JG that are not the connection: `p`-adic completeness (07JB), integrability (07JD) and
topological quasi-nilpotence (07JE) of the connection the datum determines, together with the
existence of coordinate operators that makes the last two conditions non-vacuous.  Those four
fields are carried: they are what the geometric construction of Tag 07JG proves about the
sections of a crystal, and nothing in this file derives them from the comparison datum. -/
public structure FirstOrderCrystal where
  /-- The underlying module `M`. -/
  carrier : Type uM
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its `D`-module structure. -/
  [module : Module D carrier]
  /-- The first-order comparison datum of the crystal. -/
  comparison : FirstOrderComparison A D g Omega d carrier
  /-- **Item (07JB), carried.**  The module is `p`-adically complete. -/
  isPAdicallyComplete : IsPAdicallyComplete p D carrier
  /-- **Carried.**  The connection admits coordinate operators for the chosen differentials;
  without this the next two conditions would be vacuous. -/
  hasCoordinateOperators : ∃ theta : ι → (carrier → carrier),
    IsCoordinateExpansion p D Omega dx (comparison.completedConnection p) theta
  /-- **Item (07JD), carried.**  The connection is integrable. -/
  isIntegrable : IsIntegrable p D Omega dx (comparison.completedConnection p)
  /-- **Item (07JE), carried.**  The connection is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent :
    IsTopologicallyQuasiNilpotent p D Omega dx (comparison.completedConnection p)

attribute [instance] FirstOrderCrystal.addCommGroup FirstOrderCrystal.module

/-- A morphism of first-order crystal data: a `D`-linear map compatible with the two comparison
maps. -/
@[ext] public structure FirstOrderCrystalHom
    (P Q : FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx) where
  /-- The underlying `D`-linear map. -/
  toLinearMap : P.carrier →ₗ[D] Q.carrier
  /-- Compatibility with the comparison maps. -/
  comparison_naturality : ∀ m : P.carrier, Q.comparison (toLinearMap m) =
    LinearMap.lTensor (firstOrderExtension D Omega) toLinearMap (P.comparison m)

/-- First-order crystal data and the maps compatible with their comparison maps form a
category. -/
public instance : Category (FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx) where
  Hom P Q := FirstOrderCrystalHom A D g Omega d p dx P Q
  id P := ⟨LinearMap.id, by intro m; simp⟩
  comp {P Q R} f h := ⟨h.toLinearMap ∘ₗ f.toLinearMap, by
    intro m
    have h1 := f.comparison_naturality m
    have h2 := h.comparison_naturality (f.toLinearMap m)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [h2, h1, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]⟩
  id_comp f := by apply FirstOrderCrystalHom.ext; simp
  comp_id f := by apply FirstOrderCrystalHom.ext; simp
  assoc f h k := by apply FirstOrderCrystalHom.ext; simp [LinearMap.comp_assoc]

/-! ### The functor of Tag 07JG -/

/-- A map compatible with the comparison maps is horizontal for the connections they
determine. -/
public theorem connection_naturality
    {P Q : FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx}
    (f : FirstOrderCrystalHom A D g Omega d p dx P Q) (m : P.carrier) :
    Q.comparison.connection (f.toLinearMap m) =
      LinearMap.lTensor Omega f.toLinearMap (P.comparison.connection m) := by
  simp only [FirstOrderComparison.connection, f.comparison_naturality m]
  exact firstOrderDifferentialPart_lTensor D Omega P.carrier Q.carrier f.toLinearMap
    (P.comparison m)

/-- **Stacks Project, Lemma 60.17.3, Tag 07JG**, in the affine algebraic form of this file: the
functor from first-order crystal data over `D` to the pairs `(M, ∇)` satisfying items (07JB),
(07JC), (07JD) and (07JE).  The connection of the image pair is the one the comparison datum
determines, and a map compatible with the comparison maps becomes a horizontal map.

The source of the functor is the comparison datum; the reduction of a crystal in quasi-coherent
modules on `Cris(X/S)` to that datum is not made here.  It needs the sections of `F` over the
first-order thickening as a base change of its sections over the object, which is
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`: that datum is constructed
only for `F = 𝒪_{X/S}`, and as spelled — with the algebraic tensor product of global sections
where [Stacks, Tag 07J6] names the sheaf tensor product `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` — it is false on
a general object, because `Γ` does not commute with `⊗` on a non-affine `T` (for `T = ℙ¹` over a
field of characteristic two, `Ω = 𝒪(-2)` and `F_T = 𝒪(2)`, the algebraic tensor product of
global sections vanishes while `Γ(Ω ⊗ F_T) = Γ(𝒪) ≠ 0`).

Items (07JB), (07JD), (07JE) and the existence of coordinate operators are not derived here.
They are the fields `isPAdicallyComplete`, `isIntegrable`, `isTopologicallyQuasiNilpotent` and
`hasCoordinateOperators` of `Crystalline.FirstOrderCrystal`, which the objects of the source
category supply and which this functor copies into the corresponding fields of
`Crystalline.Pair`.

`Crystalline.taylorCrystalsToPairs` factors through this functor — it is
`Crystalline.forgetToFirstOrderCrystal ⋙ firstOrderCrystalsToPairs` — but its source
`Crystalline.TaylorCrystal` replaces those four fields by the data the source's own proof works
with, the tower `M = lim_e M_e` and the composite coordinate operators `θ_K = ∏_i θ_i^{k_i}`, and
derives the three items from them. -/
public noncomputable def firstOrderCrystalsToPairs :
    FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx ⥤
      Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d) where
  obj P :=
    { carrier := P.carrier
      isPAdicallyComplete := P.isPAdicallyComplete
      nabla := P.comparison.completedConnection p
      hasCoordinateOperators := P.hasCoordinateOperators
      isIntegrable := P.isIntegrable
      isTopologicallyQuasiNilpotent := P.isTopologicallyQuasiNilpotent }
  map {P Q} f :=
    { toLinearMap := f.toLinearMap
      horizontal := by
        intro m
        change toCompletedTensor p D Omega Q.carrier
            (TensorProduct.comm D Omega Q.carrier
              (Q.comparison.connection (f.toLinearMap m))) = _
        rw [connection_naturality A D g Omega d p dx f m, comm_lTensor]
        exact (AdicCompletion.map_of (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
          (TensorProduct.map f.toLinearMap (LinearMap.id (R := (D : Type u)) (M := Omega)))
          (TensorProduct.comm D Omega P.carrier (P.comparison.connection m))).symm }
  map_id P := by apply PairHom.ext; rfl
  map_comp f h := by apply PairHom.ext; rfl

end FirstOrderThickening

end Crystalline

end
