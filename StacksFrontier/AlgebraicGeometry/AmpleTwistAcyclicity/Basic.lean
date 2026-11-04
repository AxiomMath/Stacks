module

public import StacksFrontier.AlgebraicGeometry.ProjectiveTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Serre vanishing for the powers of an ample invertible module, over an affine base

For `g : T ⟶ W` proper with `W` affine and locally Noetherian and `M` an ample invertible
`𝒪_T`-module, some `m₀` makes

`H ᵖ(T, M ^⊗ m) = 0` for every `p > 0` and every `m ≥ m₀`.

This is `Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase`, which the
dévissage of `StacksFrontier/AlgebraicGeometry/RelativeSerreVanishing/Basic.lean` turns into
[Stacks, Tag 02O1] — first into
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`, the one hypothesis
that file's proof of the tag carries, and then into the tag itself.

## The argument

It is the source's, with the projective case supplied by
`StacksFrontier/AlgebraicGeometry/ProjectiveTwistAcyclicity/Basic.lean`.

* **A closed immersion into a projective space, with the twist comparison.**
  `Stacks.AlgebraicGeometry.RelativeSerreVanishing`
  `.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple` gives a `d ≥ 1`, an `n` and a closed
  immersion `i : T ⟶ ℙⁿ_W` over `W` with `M ^⊗ d ≅ i^* 𝒪(1)`. This is the content of
  [Stacks, Tag 0B5V] together with the comparison of [Stacks, Tag 01VS]; 0B5V alone would not do,
  because it says nothing relating `M` to `i^* 𝒪(1)`.
* **The exponent is split along `d`.** Writing `m = j + d q` with `0 ≤ j < d`,
  `M ^⊗ m ≅ M ^⊗ j ⊗ i^* (𝒪(1) ^⊗ q)`: the two factors separate by
  `Stacks.Ample.tensorPowModuleAddIso`, the power of a power collapses by
  `Stacks.RelativeVeryAmple.tensorPowModulePowIso`, the comparison is transported by
  `Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso` and the inverse image is taken outside the
  power by `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. **One `q`-bound per residue `j`
  is needed, and `d` of them are taken**, their maximum being the bound in the conclusion; this is
  the step the comparison in a single degree `d` forces and it cannot be skipped.
* **The cohomology is computed upstairs.** A closed immersion is affine, so
  `H ᵖ(T, -) ≅ H ᵖ(ℙⁿ_W, i_* -)` by [Stacks, Tag 089W]
  (`Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`), and the projection formula
  `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` turns `i_*(𝒢 ⊗ i^* ℰ)` into
  `i_* 𝒢 ⊗ ℰ`. The module `i_*(M ^⊗ j)` is coherent by [Stacks, Tag 087T]
  (`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`).
* **Upstairs the dévissage already applies.** `𝒪(1)` is ample on `ℙⁿ_W` over an affine base
  (`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`) and `ℙⁿ_W ⟶ W` is proper, so
  `Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist` reduces
  the vanishing for the coherent module `i_*(M ^⊗ j)` to the vanishing for the powers of `𝒪(1)`,
  which is `Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.twistAcyclicity_projectiveSpace`.
* **Uniformity in the degree.** The dévissage fixes `p` before producing its bound, while the
  conclusion asks one bound for every `p > 0`. `exists_isZero_hgroup_tensorPowModule_of_lt` below
  reads [Stacks, Tag 01XJ] on `T` and gives a degree `e` above which every power of `M` is acyclic
  with no condition on the exponent, so only the finitely many `0 < p ≤ e` need a bound of their
  own.

## Main results

* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.exists_isZero_hgroup_tensorPowModule_of_lt`: a
  degree above which every power of `M` is acyclic, uniformly in the exponent.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`:
  **`Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase`.**
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.absoluteVanishingOverAffineBase` and
  `.vanishingOverAffineBase`: the two hypotheses of
  `StacksFrontier/AlgebraicGeometry/RelativeAmpleTwistVanishing/Basic.lean`, discharged.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity`
  `.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`: **[Stacks, Tag 02O1] with no
  hypothesis.**

## Implementation notes

**`projIsProjective` is not a `@[stacks 0B5V]`.** `isProjectiveMorphism_of_isAmple` below is the
assertion of [Stacks, Tag 0B5V] — a proper morphism carrying a relatively ample invertible module
is H-projective — and no attribute is attached to it: the tag is left to a separate
development. The declaration is a corollary of the closed immersion the argument needs
anyway and is recorded here because nothing else in the repository states it.

**Three spellings of the tensor product coincide definitionally**, and that is used rather than
transported: `Stacks.RelativeVeryAmple.tensorModules X A B`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace A B` (the spelling of
the projection formula) and `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf _ A
B` are the same term; so are `AlgebraicGeometry.Scheme.Modules.pullback f` and
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` (the spelling of
`pullbackTensorPowModuleIso`).

**The derived category.** `HasDerivedCategory.standard` is activated at priority `10000`, as in
`StacksFrontier/AlgebraicGeometry/RelativeSerreVanishing/Basic.lean` and for the same reason: the
global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is in this import closure at a lower
universe and otherwise wins.

## References

* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple RingedSpaceModuleAdjunction
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AlgebraicGeometry.AmpleTwistAcyclicity

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The degree bound on the source -/

/-- **A degree above which every power of an invertible module on `T` is acyclic.**

[Stacks, Tag 01XJ] bounds the higher direct images of every quasi-coherent module along a
quasi-compact quasi-separated morphism to a quasi-compact base by a degree depending on the
morphism alone; over an affine base the Leray degeneration
`Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus` turns that
bound into one for `H ᵖ(T, -)`. The powers are quasi-coherent by
`Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule`.

This is the companion of
`Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt`
with the coherent factor dropped, and it is what makes the bound of
`twistAcyclicityOverAffineBase` uniform in the cohomological degree. -/
theorem exists_isZero_hgroup_tensorPowModule_of_lt {T W : Scheme.{u}} (g : T ⟶ W) [IsAffine W]
    [IsProper g] (M : T.Modules) [IsInvertibleModule T M] :
    ∃ e : ℕ, ∀ p : ℕ, e < p → ∀ d : ℤ,
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorPowModule T M d)) := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward g
  refine ⟨N.toNat, fun p hp d => ?_⟩
  have hq : (tensorPowModule T M d).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule M d
  refine Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus g
    N.toNat _ (fun q hq2 => ?_) p (by omega) (by omega)
  exact hN (q : ℤ) (le_trans (Int.self_le_toNat N) (by exact_mod_cast hq2)) _ hq

/-! ### The two transports along the closed immersion -/

/-- **A twist whose invertible factor comes from the target has its cohomology computed on the
target.** For a closed immersion `i : T ⟶ Y`, a quasi-coherent `𝒢 ⊗ i^* ℰ` on `T` and a degree
`p`, vanishing of `H ᵖ(Y, i_* 𝒢 ⊗ ℰ)` gives vanishing of `H ᵖ(T, 𝒢 ⊗ i^* ℰ)`.

Two results of the library, composed. A closed immersion is affine, so [Stacks, Tag 089W]
(`Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`) identifies `H ᵖ(T, -)` with
`H ᵖ(Y, i_* -)` on quasi-coherent modules; and the projection formula
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` identifies `i_* 𝒢 ⊗ ℰ` with
`i_*(𝒢 ⊗ i^* ℰ)`. -/
theorem isZero_Hgroup_tensorModules_pullback {T Y : Scheme.{u}} (i : T ⟶ Y)
    [IsClosedImmersion i] (G : T.Modules) (E : Y.Modules) (p : ℕ)
    [(tensorModules T G ((Scheme.Modules.pullback i).obj E)).IsQuasicoherent]
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ p
      (tensorModules Y ((Scheme.Modules.pushforward i).obj G) E))) :
    IsZero (Hgroup T.ringCatSheaf ⊤ p
      (tensorModules T G ((Scheme.Modules.pullback i).obj E))) :=
  h.of_iso
    (Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp i p
        (tensorModules T G ((Scheme.Modules.pullback i).obj E)) ≪≫
      (Hfunctor Y.ringCatSheaf ⊤ p).mapIso
        (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i G E).symm)

/-- **The exponent split along the comparison degree.** If `M ^⊗ d ≅ i^* L` then

`M ^⊗ (j + d q) ≅ M ^⊗ j ⊗ i^* (L ^⊗ q)`

for all natural `j` and `q`. The two summands of the exponent separate by
`Stacks.Ample.tensorPowModuleAddIso`, the power `M ^⊗ (d q)` becomes `(M ^⊗ d) ^⊗ q` by
`Stacks.RelativeVeryAmple.tensorPowModulePowIso`, the comparison is applied inside the power by
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`, and the inverse image is moved outside the
power by `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`.

Invertibility of `i^* L` is [Stacks, Tag 0B8L]
(`Stacks.InvertiblePullback.isInvertibleModule_pullback`); it is supplied by hand because the two
power constructions are keyed on it and instance search does not cross the two spellings of the
inverse image. -/
def tensorPowModuleSplitIso {T Y : Scheme.{u}} (i : T ⟶ Y) (M : T.Modules)
    [IsInvertibleModule T M] (L : Y.Modules) [IsInvertibleModule Y L] (d : ℕ)
    (eM : tensorPowModule T M (d : ℤ) ≅ (Scheme.Modules.pullback i).obj L) (j q : ℕ) :
    tensorPowModule T M ((j : ℤ) + (d : ℤ) * (q : ℤ)) ≅
      tensorModules T (tensorPowModule T M (j : ℤ))
        ((Scheme.Modules.pullback i).obj (tensorPowModule Y L (q : ℤ))) :=
  letI : IsInvertibleModule T ((Scheme.Modules.pullback i).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback i L
  (tensorPowModuleAddIso T M (j : ℤ) ((d : ℤ) * (q : ℤ))).symm ≪≫
    tensorModulesMapIso T (Iso.refl _)
      ((tensorPowModulePowIso T M (d : ℤ) q).symm ≪≫
        tensorPowModuleIsoOfIso T (tensorPowModule T M (d : ℤ))
          ((Scheme.Modules.pullback i).obj L) eM q ≪≫
        (pullbackTensorPowModuleIso i L q).symm)

/-! ### The projective case, for one residue -/

/-- **One residue's bound.** Let `i : T ⟶ ℙⁿ_W` be a closed immersion over an affine locally
Noetherian `W`, let `M` be invertible on `T` with `M ^⊗ d ≅ i^* 𝒪(1)`, and fix `j : ℕ` and a
degree `p > 0`. Then some `q₀` makes `H ᵖ(T, M ^⊗ (j + d q)) = 0` for every `q ≥ q₀`.

The twist is moved to `ℙⁿ_W` by `tensorPowModuleSplitIso` and
`isZero_Hgroup_tensorModules_pullback`, where `i_*(M ^⊗ j)` is coherent and the dévissage
`Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist` applies,
its own hypothesis being
`Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.twistAcyclicity_projectiveSpace`. -/
theorem exists_isZero_hgroup_tensorPowModule_residue {T W : Scheme.{u}} [IsAffine W]
    [IsLocallyNoetherian W] [IsLocallyNoetherian T] {n : ℕ} (i : T ⟶ projectiveSpaceOver n W)
    [IsClosedImmersion i] (M : T.Modules) [IsInvertibleModule T M] (d : ℕ)
    (eM : tensorPowModule T M (d : ℤ) ≅
      (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n W))
    (j : ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      IsZero (Hgroup T.ringCatSheaf ⊤ p (tensorPowModule T M ((j : ℤ) + (d : ℤ) * (q : ℤ)))) := by
  have : IsProper (projectiveSpaceOver n W ↘ W) := isProper_projectiveSpaceOver n W
  have : IsLocallyNoetherian (projectiveSpaceOver n W) :=
    projectiveSpaceOver_isLocallyNoetherian n W
  have hGc : (tensorPowModule T M (j : ℤ)).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_tensorPowModule M (j : ℤ)
  have hiGc : ((Scheme.Modules.pushforward i).obj (tensorPowModule T M (j : ℤ))).IsCoherent :=
    AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion i (tensorPowModule T M (j : ℤ))
  obtain ⟨q₀, hq₀⟩ :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist
      (projectiveSpaceOver n W ↘ W) (projectiveSpaceTwistingSheaf n W)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n W)
      (Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.twistAcyclicity_projectiveSpace n W)
      ((Scheme.Modules.pushforward i).obj (tensorPowModule T M (j : ℤ))) hiGc p hp
  refine ⟨q₀, fun q hq => ?_⟩
  have : IsInvertibleModule T
      ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n W)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback i (projectiveSpaceTwistingSheaf n W)
  have hEqc : ((Scheme.Modules.pullback i).obj
      (tensorPowModule (projectiveSpaceOver n W) (projectiveSpaceTwistingSheaf n W)
        (q : ℤ))).IsQuasicoherent := by
    refine (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
      (pullbackTensorPowModuleIso i (projectiveSpaceTwistingSheaf n W) q).symm ?_
    exact Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule
      ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n W)) (q : ℤ)
  have : (tensorModules T (tensorPowModule T M (j : ℤ))
      ((Scheme.Modules.pullback i).obj
        (tensorPowModule (projectiveSpaceOver n W)
          (projectiveSpaceTwistingSheaf n W) (q : ℤ)))).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent T.toRingedSpace _ _
      (_root_.isQuasicoherent_of_isCoherent (tensorPowModule T M (j : ℤ))) hEqc
  refine (isZero_Hgroup_tensorModules_pullback i (tensorPowModule T M (j : ℤ))
    (tensorPowModule (projectiveSpaceOver n W) (projectiveSpaceTwistingSheaf n W) (q : ℤ)) p
    (hq₀ q hq)).of_iso ?_
  exact (Hfunctor T.ringCatSheaf ⊤ p).mapIso
    (tensorPowModuleSplitIso i M (projectiveSpaceTwistingSheaf n W) d eM j q)

/-! ### The hypothesis of [Stacks, Tag 02O1] -/

/-- **`Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase`.**

For `g : T ⟶ W` proper with `W` affine and locally Noetherian and `M` an ample invertible
`𝒪_T`-module, some `m₀` makes `H ᵖ(T, M ^⊗ m)` vanish for every `p > 0` and every `m ≥ m₀`.

`exists_isZero_hgroup_tensorPowModule_of_lt` reduces the degrees to the finitely many
`0 < p ≤ e`. The closed immersion `i : T ⟶ ℙⁿ_W` of
`Stacks.AlgebraicGeometry.RelativeSerreVanishing`
`.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple` compares `M ^⊗ d` with `i^* 𝒪(1)` in
one degree `d ≥ 1`, so each of the `d` residues `j = 0, …, d - 1` gets its own bound from
`exists_isZero_hgroup_tensorPowModule_residue`; the bound below is `d` times the maximum of the
finitely many `q`-bounds, plus `d`, which forces `q = m / d` past every one of them. -/
@[ega "III 2.4.1" "(ii), special case"]
theorem twistAcyclicityOverAffineBase :
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase.{u} := by
  classical
  intro T W g hWaff hWnoeth hgp M hMinv hample
  have := hWaff
  have := hWnoeth
  have := hgp
  have := hMinv
  have hTnoeth : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨e, he⟩ := exists_isZero_hgroup_tensorPowModule_of_lt g M
  obtain ⟨d, hd1, hdall⟩ :=
    RelativeSerreVanishing.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple g M hample
  obtain ⟨n, i, hi, -, ⟨eM⟩⟩ := hdall d le_rfl
  have := hi
  have key : ∀ (jj : Fin d) (ii : Fin e), ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      IsZero (Hgroup T.ringCatSheaf ⊤ ((ii : ℕ) + 1)
        (tensorPowModule T M (((jj : ℕ) : ℤ) + (d : ℤ) * (q : ℤ)))) := fun jj ii =>
    exists_isZero_hgroup_tensorPowModule_residue i M d eM (jj : ℕ) ((ii : ℕ) + 1)
      (Nat.succ_pos _)
  choose k hk using key
  refine ⟨d * ((Finset.univ.sup fun x : Fin d × Fin e => k x.1 x.2) + 1), fun m hm p hp => ?_⟩
  by_cases hpe : e < p
  · exact he p hpe (m : ℤ)
  -- `p ≤ e`, so `p = ii + 1` for an `ii : Fin e`, and the residue bound applies.
  have hdm : 0 < d := hd1
  obtain ⟨r, q, hrlt, hrq⟩ : ∃ r q : ℕ, r < d ∧ m = r + d * q :=
    ⟨m % d, m / d, Nat.mod_lt _ hdm, (Nat.mod_add_div m d).symm⟩
  let jj : Fin d := ⟨r, hrlt⟩
  let ii : Fin e := ⟨p - 1, by omega⟩
  have hidx : (ii : ℕ) + 1 = p := by simp only [ii]; omega
  have hsup : k jj ii ≤ Finset.univ.sup fun x : Fin d × Fin e => k x.1 x.2 :=
    Finset.le_sup (f := fun x : Fin d × Fin e => k x.1 x.2) (Finset.mem_univ (jj, ii))
  -- `d * (S + 1) ≤ m = r + d q < d (q + 1)` forces `S < q + 1`, i.e. `S ≤ q`.
  have hq : k jj ii ≤ q := by
    have hlt : d * ((Finset.univ.sup fun x : Fin d × Fin e => k x.1 x.2) + 1) < d * (q + 1) :=
      calc d * ((Finset.univ.sup fun x : Fin d × Fin e => k x.1 x.2) + 1)
          ≤ m := hm
        _ = r + d * q := hrq
        _ < d + d * q := Nat.add_lt_add_right hrlt (d * q)
        _ = d * (q + 1) := by ring
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have hz := hk jj ii q hq
  rw [hidx] at hz
  refine hz.of_iso ((Hfunctor T.ringCatSheaf ⊤ p).mapIso
    (tensorPowModuleCongr T M (n := (m : ℤ)) (m := (r : ℤ) + (d : ℤ) * (q : ℤ)) ?_))
  exact_mod_cast hrq

/-! ### What the hypothesis unlocks -/

/-- **[Stacks, Tag 0B5T]'s eventual-vanishing clause over an affine base, in a single degree**,
with no hypothesis: the predicate
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.AbsoluteVanishingOverAffineBase`. -/
theorem absoluteVanishingOverAffineBase :
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.AbsoluteVanishingOverAffineBase.{u} :=
  RelativeSerreVanishing.absoluteVanishingOverAffineBase_of_twistAcyclicity
    twistAcyclicityOverAffineBase

/-- **The one hypothesis of
`StacksFrontier/AlgebraicGeometry/RelativeAmpleTwistVanishing/Basic.lean`, discharged**:
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase` is a theorem. -/
theorem vanishingOverAffineBase :
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u} :=
  Stacks.AlgebraicGeometry.RelativeSerreVanishing.vanishingOverAffineBase_of_twistAcyclicity
    twistAcyclicityOverAffineBase

/-- **[Stacks, Tag 02O1], with no hypothesis.** Let `f : X ⟶ S` be a proper morphism of schemes
with `S` Noetherian, let `ℱ` be a coherent `𝒪_X`-module and let `ℒ` be an invertible
`𝒪_X`-module ample relative to `f`. Then there is an `n₀` such that for all `n ≥ n₀`,

`R ᵖ f_* (ℱ ⊗ ℒ ^⊗ n) = 0` for every `p > 0`,

with the **one** bound `n₀` serving every positive degree.

This is
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing`
`.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule` with its hypothesis `haffine`
discharged by `vanishingOverAffineBase`. -/
@[stacks 02O1]
theorem exists_isZero_rightDerivedPlus_pushforward_tensorPowModule {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsNoetherian S] [IsProper f] (F L : X.Modules) [F.IsCoherent]
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (tensorModules X F (tensorPowModule X L (n : ℤ)))) :=
  RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    vanishingOverAffineBase f F L hL

/-! ### [Stacks, Tag 0B5V] -/

/-- **A proper morphism carrying an ample invertible module is H-projective.**

This is the assertion of [Stacks, Tag 0B5V]. **No attribute is attached**: the tag is left to a
separate development, and this declaration is recorded here only because the closed
immersion the vanishing argument needs already contains it and nothing else in the repository
states it.

`Stacks.AlgebraicGeometry.RelativeSerreVanishing`
`.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple` produces the closed immersion into
`ℙⁿ_W` over `W`, which is exactly the datum
`AlgebraicGeometry.IsProjectiveMorphism` asks for. -/
theorem isProjectiveMorphism_of_isAmple {T W : Scheme.{u}} (g : T ⟶ W) [IsProper g]
    (M : T.Modules) [IsInvertibleModule T M] (hM : IsAmple T M) : IsProjectiveMorphism g := by
  obtain ⟨d, hd1, hdall⟩ :=
    RelativeSerreVanishing.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple g M hM
  obtain ⟨n, i, hi, hover, -⟩ := hdall d le_rfl
  exact ⟨n, i, hi, hover⟩

end Stacks.AlgebraicGeometry.AmpleTwistAcyclicity

end
