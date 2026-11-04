module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.ProperQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
public import StacksCore.Tactic.StacksAttribute

/-!
# Eventual vanishing of the higher direct images of a relatively ample twist

[Stacks, Tag 02O1] says: for `f : X ⟶ S` proper with `S` Noetherian, `ℱ` coherent on `X` and `ℒ`
relatively ample for `f`, there is an `n₀` such that for every `n ≥ n₀`

`R ᵖ f_* (ℱ ⊗ ℒ ^⊗ n) = 0` for all `p > 0`,

the point being that **one `n₀` serves every positive degree `p` at once**: in the source the
`n`-quantifier stands before the displayed formula and "for all `p > 0`" after it.

This file proves that statement from **one** input: the same statement over an *affine* base and
in a *single* degree. Two things separate that input from the conclusion, and both are discharged
here.

* **The base.** `S` Noetherian is quasi-compact, so it has a finite cover by affine opens, and the
  vanishing of a higher direct image is local on the base. Finiteness is what lets the finitely
  many bounds be combined into one; this is exactly the reduction the source opens with ("let
  `S = ⋃ V_j` be a finite affine open cover").
* **Uniformity in `p`.** The input is per-degree, the conclusion is not. The gap is closed by
  [Stacks, Tag 01XJ], which is proved: a quasi-compact quasi-separated morphism to a quasi-compact
  base has a degree `N`, depending on the morphism alone, above which *every* higher direct image
  of *every* quasi-coherent module vanishes. So only the finitely many degrees `0 < p < N` need a
  bound of their own, and the maximum of those is a bound for all of them.

No step of the argument uses relative ampleness beyond its definition, which already *is* "ample
on the preimage of each affine open of the base": that is why the input below is stated with
absolute ampleness, and why [Stacks, Tag 01VK]
(`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`) is not needed to reach it.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`: the single
  input — [Stacks, Tag 02O1] over an affine base, in one degree, with absolute ampleness.

## Main results

* `Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.restrictTensorPowTwistIso`: restricting a
  twist to an open is twisting the restrictions, `(ℱ ⊗ ℒ ^⊗ n)|_U ≅ ℱ|_U ⊗ (ℒ|_U) ^⊗ n`.
* `exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`, in the same namespace:
  [Stacks, Tag 02O1], with `VanishingOverAffineBase` as its one hypothesis. The hypothesis is
  proved as `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase`, in a module
  downstream of this one, and the tag is registered on the unconditional statement
  `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity`
  `.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`.

## Implementation notes

**What the one hypothesis is.** `VanishingOverAffineBase` is the relative reading, over an affine
base, of [Stacks, Tag 0B5T]'s eventual-vanishing label: absolute Serre vanishing for a proper
scheme over a Noetherian ring carrying an ample invertible sheaf, transported by
[Stacks, Tag 01XK]. It is weaker than the conclusion in the base (affine, not Noetherian), in the
ampleness (absolute, which over an affine base is what [Stacks, Tag 01VH] hands out on each
preimage), and in the degree (one `p`, not all of them at once); the implications that close
those three gaps are what this file contains. The hypothesis itself is proved as
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase` in
`StacksFrontier/AlgebraicGeometry/AmpleTwistAcyclicity/Basic.lean`, downstream of this file, and
[Stacks, Tag 02O1] is registered there, on the statement with no hypothesis.

**The twist spelling.** `Stacks.RelativeVeryAmple.tensorModules X ℱ (Stacks.Ample.tensorPowModule
X ℒ n)` is an `abbrev` for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf _ ℱ _`, which is the spelling
[Stacks, Tag 01CU]'s powers and [Stacks, Tag 01CE]'s tensor product are carried at, and the one
`Stacks.HighTwistVanishing.HasHighTwistVanishing` uses.

**Why ampleness enters through `modulePullback` and coherence through `restrictFunctor`.**
[Stacks, Tag 01VH]'s `Stacks.RelativeAmple.IsRelativelyAmple` delivers ampleness of
`(modulePullback (f ⁻¹ᵁ V).ι …).obj ℒ`, and invertibility of that is an instance
([Stacks, Tag 0B8L]); invertibility of `(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj ℒ` is
not, instance search being syntactic. The locality comparison of [Stacks, Tag 01E5], on the other
hand, is stated at `Scheme.Modules.restrictFunctor`. `restrictTensorPowTwistIso` is where the two
meet, and `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is what crosses between
them; nothing is assumed to make them agree.

**The derived category.** `HasDerivedCategory.standard` is a file-local instance, as it is in
every file of this cluster, because [Stacks, Tag 01E5]'s
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso` is elaborated with it
and carries no model parameters of its own. [Stacks, Tag 01XJ] is consumed through
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward`,
which takes its models as binders, so no instance priority is adjusted anywhere.

## References

* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction of a twist to an open -/

/-- **Restricting a twist to an open is twisting the restrictions**,
`(ℱ ⊗ ℒ ^⊗ n)|_U ≅ ℱ|_U ⊗ (ℒ|_U) ^⊗ n`.

The left-hand side restricts with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is
what the locality comparison of [Stacks, Tag 01E5] is stated at; the power on the right is taken
of the `modulePullback` of `ℒ`, which is the spelling [Stacks, Tag 01VH]'s relative ampleness
hands out and the only one whose invertibility is an instance. The crossing between the two
restriction functors is `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the
two halves of the twist are then moved separately by
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso` ([Stacks, Tag 01CD]) and
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` ([Stacks, Tag 01CU]). -/
noncomputable def restrictTensorPowTwistIso {X : Scheme.{u}} (U : X.Opens) (F L : X.Modules)
    [IsInvertibleModule X L] (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj
          (tensorModules X F (tensorPowModule X L (n : ℤ))) ≅
        tensorModules U.toScheme ((Scheme.Modules.restrictFunctor U.ι).obj F)
          (tensorPowModule U.toScheme
            ((modulePullback U.ι.toLRSHom.toShHom).obj L) (n : ℤ)) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        (tensorModules X F (tensorPowModule X L (n : ℤ))) ≪≫
      pullbackTensorModulesIso U.ι F (tensorPowModule X L (n : ℤ)) ≪≫
    tensorModulesMapIso U.toScheme
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm)
      (pullbackTensorPowModuleIso U.ι L n)

/-! ### The one input: an affine base, one degree at a time -/

/-- **[Stacks, Tag 02O1] over an affine base and in a single degree.**

For a proper morphism `g : T ⟶ W` to an affine locally Noetherian base, an ample invertible
`𝒪_T`-module `M`, a coherent `G` and **one** positive degree `p`, some `n₀` makes
`R ᵖ g_* (G ⊗ M ^⊗ n)` vanish for all `n ≥ n₀`.

This is [Stacks, Tag 0B5T]'s eventual vanishing read through [Stacks, Tag 01XK], and it is the
only thing
`exists_isZero_rightDerivedPlus_pushforward_tensorPowModule` assumes. Ampleness is the absolute
predicate of [Stacks, Tag 01PS]: over an affine base it is equivalent to relative ampleness by
[Stacks, Tag 01VK], and on the preimage of an affine open it is literally what
[Stacks, Tag 01VH] provides. -/
def VanishingOverAffineBase : Prop :=
  ∀ (T W : Scheme.{u}) (g : T ⟶ W), IsAffine W → IsLocallyNoetherian W → IsProper g →
    ∀ (M : T.Modules) [IsInvertibleModule T M], IsAmple T M →
      ∀ (G : T.Modules), G.IsCoherent → ∀ p : ℕ, 0 < p →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus (p : ℤ)).obj
            (tensorModules T G (tensorPowModule T M (n : ℤ))))

/-! ### Quasi-coherence of a twist -/

/-- A twist of a coherent module by a power of an invertible module is quasi-coherent: the
module is quasi-coherent by [Stacks, Tag 01BW], the power is by [Stacks, Tag 0B8M], and the
tensor product of two quasi-coherent modules is by [Stacks, Tag 01CE]. -/
theorem isQuasicoherent_tensorPowTwist {X : Scheme.{u}} (F L : X.Modules) [F.IsCoherent]
    [IsInvertibleModule X L] (n : ℤ) :
    (tensorModules X F (tensorPowModule X L n)).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _
    (_root_.isQuasicoherent_of_isCoherent F)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L n)

/-! ### [Stacks, Tag 02O1] -/

/-- **[Stacks, Tag 02O1], granted `VanishingOverAffineBase`.** Let `f : X ⟶ S` be a proper
morphism of schemes with `S` Noetherian, let `ℱ` be a coherent `𝒪_X`-module and let `ℒ` be an
invertible `𝒪_X`-module ample relative to `f`. Then there is an `n₀` such that for all `n ≥ n₀`,

`R ᵖ f_* (ℱ ⊗ ℒ ^⊗ n) = 0` for every `p > 0`,

with the **one** bound `n₀` serving every positive degree.

Granted `VanishingOverAffineBase`, which is the same assertion over an affine base and for a
single degree. The two gaps it leaves are closed as follows.

*Degrees.* [Stacks, Tag 01XJ], available as
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward`,
gives a degree `N` depending only on `f` above which every higher direct image of every
quasi-coherent module vanishes — and a twist is quasi-coherent, by `isQuasicoherent_tensorPowTwist`.
So the degrees needing their own bound are the finitely many `0 < p < N`.

*Base.* `S` is Noetherian, hence quasi-compact, so
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_fin_affineOpen_cover` gives a **finite**
cover of `S` by affine opens. Over each member the hypothesis applies — properness and local
Noetherianness restrict, coherence of `ℱ` restricts by
`AlgebraicGeometry.Modules.isCoherent_restrict`, and ampleness of the restriction of `ℒ` is the
second component of [Stacks, Tag 01VH]'s relative ampleness — and `restrictTensorPowTwistIso`
identifies the twist of the restrictions with the restriction of the twist. The conclusions are
carried back to `V` by [Stacks, Tag 01E5]
(`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`) and glued by
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover`.

Finiteness of the cover and finiteness of the degree range are both essential: the single bound is
the maximum of the bounds over the product of the two finite index sets. -/
theorem exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    (haffine : VanishingOverAffineBase.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsNoetherian S] [IsProper f] (F L : X.Modules) [F.IsCoherent]
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (tensorModules X F (tensorPowModule X L (n : ℤ)))) := by
  classical
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward f
  obtain ⟨m, B, hBaff, hBcover⟩ :=
    Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_fin_affineOpen_cover S
  -- Over each member of the cover, and in each of the finitely many degrees below `N`, the
  -- hypothesis supplies a bound.
  have key : ∀ (j : Fin m) (i : Fin N.toNat), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (((Scheme.Modules.pushforward (f ∣_ B j)).rightDerivedPlus
          (((i : ℕ) + 1 : ℕ) : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ B j).ι).obj
          (tensorModules X F (tensorPowModule X L (n : ℤ))))) := by
    intro j i
    have hWaff : IsAffine (B j).toScheme := hBaff j
    obtain ⟨n₀, hn₀⟩ := haffine _ _ (f ∣_ B j) hWaff inferInstance inferInstance
      ((modulePullback (f ⁻¹ᵁ B j).ι.toLRSHom.toShHom).obj L) (hL.2 (B j) (hBaff j))
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ B j).ι).obj F)
      (Modules.isCoherent_restrict F (f ⁻¹ᵁ B j)) ((i : ℕ) + 1) (Nat.succ_pos _)
    refine ⟨n₀, fun n hn => ?_⟩
    exact IsZero.of_iso (hn₀ n hn)
      (((Scheme.Modules.pushforward (f ∣_ B j)).rightDerivedPlus (((i : ℕ) + 1 : ℕ) : ℤ)).mapIso
        (restrictTensorPowTwistIso (f ⁻¹ᵁ B j) F L n))
  choose k hk using key
  refine ⟨Finset.univ.sup fun jp : Fin m × Fin N.toNat => k jp.1 jp.2, fun n p hn hp => ?_⟩
  by_cases hpN : N ≤ (p : ℤ)
  · -- Above the uniform degree of [Stacks, Tag 01XJ] nothing need be assumed at all.
    exact hN (p : ℤ) hpN _ (isQuasicoherent_tensorPowTwist F L (n : ℤ))
  · -- Below it, glue the finitely many affine conclusions.
    have hpN' : p < N.toNat := by omega
    let q : Fin N.toNat := ⟨p - 1, by omega⟩
    have hqv : (q : ℕ) = p - 1 := rfl
    have hidx : (q : ℕ) + 1 = p := by omega
    refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover B
      hBcover _ fun j => ?_
    have hbound : k j q ≤ n :=
      le_trans (Finset.le_sup (f := fun jp : Fin m × Fin N.toNat => k jp.1 jp.2)
        (Finset.mem_univ (j, q))) hn
    have hz := hk j q n hbound
    rw [hidx] at hz
    exact IsZero.of_iso hz
      (ProjectiveCoherentImage.higherDirectImageRestrictObjIso f (B j)
        (tensorModules X F (tensorPowModule X L (n : ℤ))) p).symm

/-! ### The input pushed back to absolute cohomology

[Stacks, Tag 01XK] is proved, so `VanishingOverAffineBase` — which is phrased with the *relative*
`R ᵖ g_*` — can be replaced by the *absolute* statement about `H ᵖ(T, ·)`, which is the literal
shape of [Stacks, Tag 0B5T]'s eventual-vanishing label. That is strictly weaker, and it is
phrased as a Stacks tag rather than as "Tag 02O1 over an affine base". -/

/-- **[Stacks, Tag 0B5T]'s eventual-vanishing label over an affine base, one degree at a time.**

For `T` proper over an affine locally Noetherian `W`, an ample invertible `M` on `T`, a coherent
`G` and **one** positive degree `p`, some `n₀` makes `H ᵖ(T, G ⊗ M ^⊗ n)` vanish for all `n ≥ n₀`.

This is absolute Serre vanishing. It is proved as
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.absoluteVanishingOverAffineBase`, in a module
downstream of this one. Compare `Stacks.HighTwistVanishing.HasHighTwistVanishing`, which is this
statement with the degree quantified *inside* the bound; only closure properties are proved of
it. -/
def AbsoluteVanishingOverAffineBase : Prop :=
  ∀ (T W : Scheme.{u}) (g : T ⟶ W), IsAffine W → IsLocallyNoetherian W → IsProper g →
    ∀ (M : T.Modules) [IsInvertibleModule T M], IsAmple T M →
      ∀ (G : T.Modules), G.IsCoherent → ∀ p : ℕ, 0 < p →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          IsZero (Hgroup T.ringCatSheaf ⊤ p
            (tensorModules T G (tensorPowModule T M (n : ℤ))))

/-- **Over an affine base, absolute vanishing gives relative vanishing**: the hypothesis of
`exists_isZero_rightDerivedPlus_pushforward_tensorPowModule` follows from the absolute
[Stacks, Tag 0B5T] statement.

Three results do it. `H ᵖ(T, ·)` as an abelian group and as a module of sections vanish
together (`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`,
and `Stacks.Cohomology.sectionsFunctor T ⊤` *is* the evaluation functor at `⊤`). Over an affine
base, [Stacks, Tag 01XK] identifies that module of sections, after restriction of scalars along
`g^#`, with the global sections of `R ᵖ g_*` of the same module — this is
`Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward`, applied at the twist
regarded as an object of the quasi-coherent subcategory. Finally `R ᵖ g_*` of a quasi-coherent
module is quasi-coherent along a proper morphism ([Stacks, Tag 01XJ] part (1), through
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`), and a
quasi-coherent module on an affine scheme with no global sections is a zero object
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine`). The
degree is converted between the `ℕ`- and `ℤ`-indexed derived functors by
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`. -/
theorem vanishingOverAffineBase_of_absolute
    (habs : AbsoluteVanishingOverAffineBase.{u}) : VanishingOverAffineBase.{u} := by
  intro T W g hWaff hWnoeth hgp M hMinv hample G hG p hp
  have := hMinv
  have := hG
  have := hgp
  have := hWaff
  obtain ⟨n₀, hn₀⟩ := habs T W g hWaff hWnoeth hgp M hample G hG p hp
  refine ⟨n₀, fun n hn => ?_⟩
  have hHq : (tensorModules T G (tensorPowModule T M (n : ℤ))).IsQuasicoherent :=
    isQuasicoherent_tensorPowTwist G M (n : ℤ)
  -- Group-valued and module-valued cohomology over `⊤` vanish together.
  have hmod : IsZero (((Stacks.Cohomology.sectionsFunctor T ⊤).rightDerived p).obj
      (tensorModules T G (tensorPowModule T M (n : ℤ)))) :=
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      T.ringCatSheaf ⊤ p _).mpr (hn₀ n hn)
  have hplus : IsZero (((Stacks.Cohomology.sectionsFunctor T ⊤).rightDerivedPlus (p : ℤ)).obj
      (tensorModules T G (tensorPowModule T M (n : ℤ)))) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Stacks.Cohomology.sectionsFunctor T ⊤) p _).mp hmod
  have hres : IsZero ((ModuleCat.restrictScalars
      (CommRingCat.Hom.hom (Scheme.Hom.appTop g))).obj
      (((Stacks.Cohomology.sectionsFunctor T ⊤).rightDerivedPlus (p : ℤ)).obj
        (tensorModules T G (tensorPowModule T M (n : ℤ))))) :=
    Functor.map_isZero _ hplus
  -- [Stacks, Tag 01XK] carries it to the global sections of the higher direct image.
  have hiso := (Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward g
    (p : ℤ)).app
      (⟨tensorModules T G (tensorPowModule T M (n : ℤ)), hHq⟩ :
        (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory)
  have hsec : IsZero ((Stacks.Cohomology.sectionsFunctor W ⊤).obj
      (((Scheme.Modules.pushforward g).rightDerivedPlus (p : ℤ)).obj
        (tensorModules T G (tensorPowModule T M (n : ℤ))))) := hres.of_iso hiso.symm
  have : (((Scheme.Modules.pushforward g).rightDerivedPlus (p : ℤ)).obj
      (tensorModules T G (tensorPowModule T M (n : ℤ)))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent g _ (p : ℤ)
  exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _ hsec

/-- **[Stacks, Tag 02O1] from absolute Serre vanishing.** The composite of
`vanishingOverAffineBase_of_absolute` with
`exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`: the conclusion of
[Stacks, Tag 02O1], with its bound uniform in `p`, from the single input
`AbsoluteVanishingOverAffineBase` — [Stacks, Tag 0B5T] over an affine base, in one degree. This
is the weakest hypothesis under which this file proves the tag. -/
theorem exists_isZero_rightDerivedPlus_pushforward_tensorPowModule_of_absolute
    (habs : AbsoluteVanishingOverAffineBase.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsNoetherian S] [IsProper f] (F L : X.Modules) [F.IsCoherent]
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (tensorModules X F (tensorPowModule X L (n : ℤ)))) :=
  exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    (vanishingOverAffineBase_of_absolute habs) f F L hL

end Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing

end
