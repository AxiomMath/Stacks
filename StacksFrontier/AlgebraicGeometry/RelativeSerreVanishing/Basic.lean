module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleTwistVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.FiniteSum
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.AffineFromNegativeTwists
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.ChowConsumption
public import StacksFrontier.AlgebraicGeometry.ReflexiveExtensionGate.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative Serre vanishing reduced to the tensor powers of the ample module

[Stacks, Tag 02O1] is proved in `../RelativeAmpleTwistVanishing/Basic.lean` from a single input,
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`, whose absolute
form `AbsoluteVanishingOverAffineBase` is [Stacks, Tag 0B5T]'s eventual-vanishing clause over an
affine base: for `T` proper over an affine locally Noetherian `W`, `M` ample invertible on `T`,
`G` **coherent** and one `p > 0`, some `n₀` makes `H ᵖ(T, G ⊗ M ^⊗ n)` vanish for `n ≥ n₀`.

This file removes the coherent module from that hypothesis. What is left is the same assertion
with `G` taken to be the structure sheaf, i.e. eventual vanishing for the *tensor powers of `M`
alone*:

`H ᵖ(T, M ^⊗ m) = 0` for all `p > 0` and all `m ≫ 0`.

`Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase` names that, and
`absoluteVanishingOverAffineBase_of_twistAcyclicity` proves the hypothesis of
[Stacks, Tag 02O1] from it. Composing with the two bridges already proved in
`../RelativeAmpleTwistVanishing/Basic.lean` gives [Stacks, Tag 02O1] itself from this one input.

## The reduction

It is the source's own dévissage, run on `T` rather than on a projective space, and every piece
of it is formalized.

* **The presentation.** Clause (8) of [Stacks, Tag 01Q3] holds on any scheme with an ample
  invertible module, unconditionally
  (`Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple` feeding
  `Stacks.AmpleGlobalGeneration.isQuotientOfNegativeTwists_of_isEventuallyGloballyGenerated`):
  every finite-type quasi-coherent `G` sits in a short exact sequence
  `0 → G' → ⨁_{j ∈ Fin r} M ^⊗ (-dⱼ) → G → 0`. A coherent module is quasi-coherent and of
  finite type, so the sequence is available for it; the middle term is a finite direct sum of
  invertible modules, hence coherent on a locally Noetherian scheme, and the first term is then
  coherent because it is the kernel of a map of coherent modules.
* **The middle term is eventually acyclic.** `M ^⊗ (-dⱼ) ⊗ M ^⊗ d ≅ M ^⊗ (d - dⱼ)`
  (`Stacks.Ample.tensorPowModuleAddIso`), and the index set is finite, so the hypothesis gives
  one `d₀` beyond which every summand is acyclic in every positive degree; additivity of
  `H ᵖ(T, (-) ⊗ M ^⊗ d)` carries that to the direct sum.
* **Twisting preserves the sequence.** Tensoring by an invertible module is an autoequivalence
  (`Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight`).
* **The descending induction has a floor.** [Stacks, Tag 01XJ] gives a degree `N`, depending on
  the structure morphism alone, above which every higher direct image of every quasi-coherent
  module vanishes; over an affine base the Leray degeneration
  `Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus` turns that
  into a vanishing bound for `H ᵖ(T, -)` itself, uniformly in the twist.

Those four facts are exactly the hypotheses of
`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage`, the engine
[Stacks, Tag 01YS] clause (4) and [Stacks, Tag 0B5Q] clause (3) are both proved by.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase`: eventual
  vanishing of the higher cohomology of the tensor powers of an ample invertible module on a
  scheme proper over an affine locally Noetherian base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist`: the
  dévissage — the vanishing for every coherent module, from the vanishing for the powers.
* `absoluteVanishingOverAffineBase_of_twistAcyclicity`,
  `vanishingOverAffineBase_of_twistAcyclicity` and
  `exists_isZero_rightDerivedPlus_pushforward_tensorPowModule_of_twistAcyclicity`, in the same
  namespace: the two hypotheses of `../RelativeAmpleTwistVanishing/Basic.lean` and the conclusion
  of [Stacks, Tag 02O1], each from `TwistAcyclicityOverAffineBase`.

## Implementation notes

**Where the remaining input is proved.** `TwistAcyclicityOverAffineBase` is strictly weaker than
the hypothesis it replaces — it is the case `G = 𝒪_T` of it — and it is **not** proved here. It is
proved in `StacksFrontier/AlgebraicGeometry/AmpleTwistAcyclicity/Basic.lean`, as
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`, so everything in
this file is unconditional through that composite.

Every step of the route is formalized.

* `exists_isClosedImmersion_projectiveSpaceOver_of_isAmple`, below, gives the closed immersion
  `i : T ⟶ ℙⁿ_W` over `W` with `M ^⊗ d ≅ i^* 𝒪(1)`.
* `M ^⊗ (j + dq) ≅ M ^⊗ j ⊗ i^* (𝒪(1) ^⊗ q)` by `Stacks.Ample.tensorPowModuleAddIso`,
  `Stacks.RelativeVeryAmple.tensorPowModulePowIso`, `…tensorPowModuleIsoOfIso` and
  `…pullbackTensorPowModuleIso`, and one `q`-bound is taken for each of the `d` residues `j`.
* `H ᵖ(T, -) ≅ H ᵖ(ℙⁿ_W, i_* -)` is [Stacks, Tag 089W],
  `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`, a closed immersion being
  affine; the projection formula `i_*(𝒢 ⊗ i^* ℰ) ≅ i_* 𝒢 ⊗ ℰ` is
  `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`; and `i_* (M ^⊗ j)` is
  coherent by `AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`.
* The resulting statement on `ℙⁿ_W` is about a coherent module, and
  `exists_isZero_hgroup_tensorPowTwist` above reduces that back to the twists of `𝒪(1)`, which is
  `Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.twistAcyclicity_projectiveSpace`.

**The projective instance.** Serre vanishing is first proved for the *other* model of `ℙⁿ_R`,
`AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)`
(`Stacks.ProjectiveSpace.SerreVanishing.isZero_Hgroup_twistingSheaf_of_pos`), and transporting
it to `AlgebraicGeometry.projectiveSpaceOver` needs the *twisting sheaf* half of clause (3) of
[Stacks, Tag 01N2]. That clause is a theorem,
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport`, and the transport is
`StacksFrontier/AlgebraicGeometry/ProjectiveTwistAcyclicity/Basic.lean`.

**The degree stays inside the bound.** The conclusion of the dévissage engine fixes `p` before
producing `d₀`, which is why both this file's hypothesis and `AbsoluteVanishingOverAffineBase`
quantify one `p` at a time. Making the bound uniform in `p` is what
`../RelativeAmpleTwistVanishing/Basic.lean` does with [Stacks, Tag 01XJ], and it is not redone
here.

**The derived category.** `HasDerivedCategory.standard` is activated at priority `10000` rather
than at the default: the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is in this
import closure and is at a lower universe, so a plain `attribute [local instance]` leaves it
winning and `rightDerivedPlus` silently elaborates at the wrong universes.

## References

* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe u

namespace Stacks.AlgebraicGeometry.RelativeSerreVanishing

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Coherence of the terms of the dévissage sequence -/

/-- Alias of `Stacks.AlgebraicGeometry.ReflexiveExtensionGate.isCoherent_of_iso`. -/
alias isCoherent_of_iso := Stacks.AlgebraicGeometry.ReflexiveExtensionGate.isCoherent_of_iso

/-- **A tensor power of an invertible module on a locally Noetherian scheme is coherent.** The
power is invertible (`Stacks.Ample.isInvertibleModule_tensorPowModule`, [Stacks, Tag 0B8L]) and an
invertible module on a locally Noetherian scheme is coherent ([Stacks, Tag 01XZ]).

The two sheaf-condition arguments are `Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X`,
which `Stacks.Ample.IsInvertibleModule` supplies, and `X.ringCatSheaf.2`, which
[Stacks, Tag 01XZ] is stated with; they are the same proposition, so the `have` crosses between
them, while instance search — being syntactic — does not. -/
@[sga "6 I 3.6" "more general"]
theorem isCoherent_tensorPowModule {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [IsInvertibleModule X L] (n : ℤ) : (tensorPowModule X L n).IsCoherent := by
  have h : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (isSheaf_structureRingPresheaf X) (tensorPowModule X L n) :=
    isInvertibleModule_tensorPowModule X L n
  exact @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
    (tensorPowModule X L n) h

/-! ### The twist functor

`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` asks for the twist
as a family of endofunctors of `SheafOfModules X.ringCatSheaf`. The degree-`d` twist uses
the native sheaf tensor bifunctor with `L ^⊗ d` fixed in the right factor. The two instances
below supply its existing zero-preservation and additivity laws from
`Stacks.AmpleCohomologicalCriterion`. -/

/-- **Tensoring on the right by the `d`-th tensor power of an invertible module**, as an
endofunctor of `SheafOfModules X.ringCatSheaf` — the twist the descending dévissage is run
along. -/
@[sga "7 XI 1.0" "more general"]
def twistFunctor {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (d : ℤ) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
    (tensorPowModule X L d)

/-- The value of `twistFunctor` is the tensor product of [Stacks, Tag 05NA], which is the
spelling `AbsoluteVanishingOverAffineBase` states the twist at. -/
theorem twistFunctor_obj {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (d : ℤ)
    (F : X.Modules) :
    (twistFunctor L d).obj F = tensorModules X F (tensorPowModule X L d) := rfl

/-- `twistFunctor L d` preserves zero morphisms. -/
instance preservesZeroMorphisms_twistFunctor {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) : (twistFunctor L d).PreservesZeroMorphisms :=
  Stacks.AmpleCohomologicalCriterion.preservesZeroMorphisms_tensorRight X _

/-- `twistFunctor L d` is additive. -/
instance additive_twistFunctor {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
    (d : ℤ) : (twistFunctor L d).Additive :=
  Stacks.AmpleCohomologicalCriterion.additive_tensorRight X _

/-- The cohomology functor `Hfunctor X.ringCatSheaf U n` on `𝒪_X`-modules is additive. -/
instance additive_hfunctor_scheme {X : Scheme.{u}} (U : X.Opens) (n : ℕ) :
    (Hfunctor X.ringCatSheaf U n).Additive :=
  Stacks.HighTwistDevissage.additive_hfunctor X U n

/-- **A finite direct sum of coherent modules is coherent**, for a direct sum presented as a
bicone rather than by `⨁`. The bicone presentation is the one clause (8) of [Stacks, Tag 01Q3] is
stated at, and the one `Stacks.HighTwistDevissage.isZero_obj_of_isBilimit` consumes. -/
theorem isCoherent_bicone {X : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type} [Finite ι]
    {f : ι → X.Modules} {b : Bicone f} (hb : b.IsBilimit) (hf : ∀ i, (f i).IsCoherent) :
    b.pt.IsCoherent := by
  have : HasBiproduct f := HasBiproduct.mk ⟨b, hb⟩
  have hsig : Stacks.SheafOfModules.IsCoherent (∐ f) :=
    Stacks.SheafOfModules.isCoherent_sigma f fun i =>
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hf i)
  refine AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent ?_
  exact (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso
    ((biproduct.isoCoproduct f).symm.trans (biproduct.uniqueUpToIso f hb).symm) hsig

/-- **The sub term of a short exact sequence of coherent modules is coherent.** It is the kernel
of the sequence's second map up to the canonical comparison of limit cones, and the kernel of a
map of coherent modules on a locally Noetherian scheme is coherent. -/
theorem isCoherent_X₁ {X : Scheme.{u}} [IsLocallyNoetherian X] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent) : S.X₁.IsCoherent := by
  have e : S.X₁ ≅ kernel S.g := IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit _)
  have hk : (kernel S.g).IsCoherent := by
    have := h₂
    have := h₃
    exact AlgebraicGeometry.isCoherent_kernel S.g
  exact isCoherent_of_iso e.symm hk

/-! ### The remaining input: the tensor powers alone -/

/-- **Eventual vanishing of the higher cohomology of the tensor powers of an ample invertible
module, over an affine base.**

For `g : T ⟶ W` proper with `W` affine and locally Noetherian and `M` an ample invertible
`𝒪_T`-module, some `m₀` makes `H ᵖ(T, M ^⊗ m)` vanish for every `p > 0` and every `m ≥ m₀`.

This is the case `G = 𝒪_T` of
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.AbsoluteVanishingOverAffineBase`, and
`absoluteVanishingOverAffineBase_of_twistAcyclicity` recovers the general case from it. Unlike
that predicate it mentions no coherent module and no tensor product: the only modules in it are
the powers of `M`. It is proved, with no hypothesis, by
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`. -/
def TwistAcyclicityOverAffineBase : Prop :=
  ∀ (T W : Scheme.{u}) (g : T ⟶ W), IsAffine W → IsLocallyNoetherian W → IsProper g →
    ∀ (M : T.Modules) [IsInvertibleModule T M], IsAmple T M →
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ p : ℕ, 0 < p →
        IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorPowModule T M (m : ℤ)))

/-! ### The vanishing bound of [Stacks, Tag 01XJ], read on `T` -/

/-- **A vanishing degree for `H ᵖ(T, -)` on the twists, uniform in the module and in the twist.**
[Stacks, Tag 01XJ] bounds the higher direct images of every quasi-coherent module along a
quasi-compact quasi-separated morphism to a quasi-compact base by a degree depending on the
morphism alone; over an affine base the Leray degeneration of
`Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus` turns that
bound into one for the cohomology of `T` itself. The twists are quasi-coherent by
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist`.

This is the `hbound` input of the descending dévissage: it is what gives the induction on the
cohomological degree somewhere to start. -/
theorem exists_isZero_hgroup_tensorPowTwist_of_lt {T W : Scheme.{u}} (g : T ⟶ W) [IsAffine W]
    [IsProper g] (M : T.Modules) [IsInvertibleModule T M] :
    ∃ e : ℕ, ∀ p : ℕ, e < p → ∀ F : T.Modules, F.IsCoherent → ∀ d : ℤ,
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorModules T F (tensorPowModule T M d))) := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward g
  refine ⟨N.toNat, fun p hp F hF d => ?_⟩
  have hq : (tensorModules T F (tensorPowModule T M d)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist
      (F := F) (L := M) d
  refine Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus g
    N.toNat _ (fun q hq2 => ?_) p (by omega) (by omega)
  exact hN (q : ℤ) (by omega) _ hq

/-! ### The dévissage -/

/-- **The `step` input of the descending dévissage.** Every coherent `𝒪_T`-module `F` is the
quotient term of a short exact sequence whose sub term is again coherent, whose every twist by a
power of `M` is short exact, and whose middle term has vanishing higher cohomology after every
sufficiently positive twist.

The sequence is clause (8) of [Stacks, Tag 01Q3], proved unconditionally from ampleness; its
middle term is `⨁_{j ∈ Fin r} M ^⊗ (-dⱼ)`, each summand becomes `M ^⊗ (d - dⱼ)` after the twist
by `M ^⊗ d`, and `Fin r` is finite, so one `d₀` serves them all. -/
theorem step_of_twistAcyclicity {T : Scheme.{u}} [IsLocallyNoetherian T] (M : T.Modules)
    [IsInvertibleModule T M] (hM : IsAmple T M)
    (htw : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorPowModule T M (m : ℤ))))
    (F : SheafOfModules.{u} T.ringCatSheaf) (hF : F.IsCoherent) :
    ∃ S : ShortComplex (SheafOfModules.{u} T.ringCatSheaf), S.X₃ = F ∧ S.X₁.IsCoherent ∧
      (∀ d : ℤ, (S.map (twistFunctor M d)).ShortExact) ∧
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
        IsZero (Hgroup T.ringCatSheaf ⊤ m ((twistFunctor M d).obj S.X₂)) := by
  classical
  obtain ⟨m₀, hm₀⟩ := htw
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨S, r, dj, b, hb, e, hse, hX₃, -, hdj⟩ :=
    Stacks.AmpleGlobalGeneration.isQuotientOfNegativeTwists_of_isEventuallyGloballyGenerated
      (Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple M hM)
      0 F hqc hF.isFiniteType
  have hptc : b.pt.IsCoherent :=
    isCoherent_bicone hb fun j => isCoherent_tensorPowModule M (-dj j)
  have hX₂ : S.X₂.IsCoherent := isCoherent_of_iso e.symm hptc
  have hX₃c : S.X₃.IsCoherent := hX₃ ▸ hF
  refine ⟨S, hX₃, isCoherent_X₁ hse hX₂ hX₃c, fun d => ?_, ?_⟩
  · exact Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight T _ hse
  refine ⟨(m₀ : ℤ) + (Finset.univ.sup fun j : Fin r => (dj j).toNat : ℕ), fun d hd m hm => ?_⟩
  refine IsZero.of_iso ?_ ((twistFunctor M d ⋙ Hfunctor T.ringCatSheaf ⊤ m).mapIso e)
  refine Stacks.HighTwistDevissage.isZero_obj_of_isBilimit
    (twistFunctor M d ⋙ Hfunctor T.ringCatSheaf ⊤ m) hb inferInstance fun j => ?_
  have hsup : (dj j).toNat ≤ (Finset.univ.sup fun k : Fin r => (dj k).toNat) :=
    Finset.le_sup (f := fun k : Fin r => (dj k).toNat) (Finset.mem_univ j)
  have hdj0 : 0 ≤ dj j := hdj j
  have hnat : -dj j + d = ((d - dj j).toNat : ℤ) := by omega
  have key : IsZero (Hgroup T.ringCatSheaf ⊤ m (tensorPowModule T M (-dj j + d))) := by
    rw [hnat]
    exact hm₀ (d - dj j).toNat (by omega) m hm
  exact key.of_iso ((Hfunctor T.ringCatSheaf ⊤ m).mapIso (tensorPowModuleAddIso T M (-dj j) d))

/-- **The dévissage.** On a scheme proper over an affine locally Noetherian base and carrying an
ample invertible `M`, eventual vanishing of the higher cohomology of the powers of `M` gives
eventual vanishing of the higher cohomology of the `M`-twists of **every coherent module**.

This is `Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` — the
engine [Stacks, Tag 01YS] clause (4) is proved by — at the twist functor
`(-) ⊗ M ^⊗ d`, the class of coherent modules, the bound of
`exists_isZero_hgroup_tensorPowTwist_of_lt` and the sequence of `step_of_twistAcyclicity`. -/
theorem exists_isZero_hgroup_tensorPowTwist {T W : Scheme.{u}} (g : T ⟶ W) [IsAffine W]
    [IsLocallyNoetherian W] [IsProper g] (M : T.Modules) [IsInvertibleModule T M]
    (hM : IsAmple T M)
    (htw : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorPowModule T M (m : ℤ))))
    (G : T.Modules) (hG : G.IsCoherent) (p : ℕ) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorModules T G (tensorPowModule T M (n : ℤ)))) := by
  have hTnoeth : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨e, he⟩ := exists_isZero_hgroup_tensorPowTwist_of_lt g M
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage
      T.ringCatSheaf ⊤
      (fun d => twistFunctor M d)
      (fun F => F.IsCoherent) e he (step_of_twistAcyclicity M hM htw) p hp G hG
  exact ⟨d₀.toNat, fun n hn => hd₀ (n : ℤ) (by omega)⟩

/-! ### A closed immersion into projective space, with the twist comparison -/

/-- **Over any base, a proper morphism carrying an ample invertible module admits a closed
immersion into a projective space pulling `𝒪(1)` back to a tensor power of the module.**

For `g : T ⟶ W` proper and `M` an ample invertible `𝒪_T`-module there is a `d₀ ≥ 1` such that
every `d ≥ d₀` admits an `n` and a **closed** immersion `i : T ⟶ ℙⁿ_W` over `W` with
`M ^⊗ d ≅ i^* 𝒪(1)`.

[Stacks, Tag 01VS] (`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`)
gives an immersion, properness of `g` being more than the locally-finite-type hypothesis it asks
for. The upgrade to a closed immersion is [Stacks, Tag 0201]'s: `ℙⁿ_W` is separated over `W`
(`Stacks.HProjective.isSeparated_over`), so `i` is proper by `AlgebraicGeometry.IsProper.of_comp`,
and a proper immersion is closed
(`AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper`).

This is the input [Stacks, Tag 0B5V] does not supply: 0B5V produces a closed immersion into some
projective space but says nothing comparing `M` with `i^* 𝒪(1)`, and without that comparison an
`M`-twist cannot be turned into the `𝒪(1)`-twist a projective-space vanishing theorem is about. -/
theorem exists_isClosedImmersion_projectiveSpaceOver_of_isAmple {T W : Scheme.{u}} (g : T ⟶ W)
    [IsProper g] (M : T.Modules) [IsInvertibleModule T M] (hM : IsAmple T M) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : T ⟶ projectiveSpaceOver n W), IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver n W ↘ W) = g ∧
        Nonempty (tensorPowModule T M (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n W)) := by
  obtain ⟨d₀, hd₀, h⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple g M hM
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  obtain ⟨n, i, hi, hcomm, hiso⟩ := h d hd
  have _hi : IsImmersion i := hi
  have _hp : IsProper (i ≫ (projectiveSpaceOver n W ↘ W)) := by
    rw [Stacks.HProjective.over_projectiveSpaceOver, hcomm]
    infer_instance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver n W ↘ W)
  exact ⟨n, i, AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper i,
    (Stacks.HProjective.over_projectiveSpaceOver n W).symm ▸ hcomm, hiso⟩

/-! ### The inputs of [Stacks, Tag 02O1] -/

/-- **[Stacks, Tag 0B5T]'s eventual-vanishing clause over an affine base, from the powers
alone.** `Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.AbsoluteVanishingOverAffineBase`
follows from `TwistAcyclicityOverAffineBase`: the coherent module is removed from the hypothesis
by the dévissage of `exists_isZero_hgroup_tensorPowTwist`. -/
theorem absoluteVanishingOverAffineBase_of_twistAcyclicity
    (htw : TwistAcyclicityOverAffineBase.{u}) :
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.AbsoluteVanishingOverAffineBase.{u} := by
  intro T W g hWaff hWnoeth hgp M hMinv hample G hG p hp
  have := hWaff
  have := hWnoeth
  have := hgp
  exact exists_isZero_hgroup_tensorPowTwist g M hample
    (htw T W g hWaff hWnoeth hgp M hample) G hG p hp

/-- **The hypothesis of [Stacks, Tag 02O1], from the powers alone.**
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase` follows from
`TwistAcyclicityOverAffineBase`, by the dévissage above and the [Stacks, Tag 01XK] bridge
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.vanishingOverAffineBase_of_absolute`. -/
theorem vanishingOverAffineBase_of_twistAcyclicity
    (htw : TwistAcyclicityOverAffineBase.{u}) :
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u} :=
  Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.vanishingOverAffineBase_of_absolute
    (absoluteVanishingOverAffineBase_of_twistAcyclicity htw)

/-- **[Stacks, Tag 02O1] from the powers alone.** Let `f : X ⟶ S` be proper with `S` Noetherian,
`ℱ` coherent and `ℒ` invertible and ample relative to `f`. Then one `n₀` makes
`R ᵖ f_* (ℱ ⊗ ℒ ^⊗ n)` vanish for every `n ≥ n₀` and **every** `p > 0` at once.

The composite of `vanishingOverAffineBase_of_twistAcyclicity` with
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing`
`.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`. This is the weakest hypothesis
under which the tag is currently proved: it asks nothing of any coherent module, only of the
tensor powers of the ample module itself, over an affine base, and in a single degree.

No attribute is attached here. The hypothesis is discharged in
`StacksFrontier/AlgebraicGeometry/AmpleTwistAcyclicity/Basic.lean`, and the covering set for the tag
is the hypothesis-free statement there,
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity`
`.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`. -/
theorem exists_isZero_rightDerivedPlus_pushforward_tensorPowModule_of_twistAcyclicity
    (htw : TwistAcyclicityOverAffineBase.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsNoetherian S] [IsProper f] (F L : X.Modules) [F.IsCoherent]
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (tensorModules X F (tensorPowModule X L (n : ℤ)))) :=
  RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    (vanishingOverAffineBase_of_twistAcyclicity htw) f F L hL

end Stacks.AlgebraicGeometry.RelativeSerreVanishing

end
