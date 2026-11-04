module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Properties.IdealPowerAnnihilatorQuasicoherent

/-!
# Separating a quasi-coherent torsion subsheaf from a high ideal power

Let `X` be a Noetherian scheme, `F` a coherent `𝒪_X`-module, `I ⊆ 𝒪_X` a quasi-coherent sheaf of
ideals and `G ⊆ F` a quasi-coherent subsheaf which is annihilated by `I ^ n`. Artin–Rees then
separates `G` from a sufficiently high ideal power: there is an `m` with

`I ^ m F ⊓ G = 0`.

Indeed Artin–Rees supplies a single `c` with `I ^ m F ⊓ G = I ^ (m - c) (I ^ c F ⊓ G)` for all
`m ≥ c`, and taking `m = n + c` bounds the right-hand side by `I ^ n G`, which is zero.

This is the step on which the surjectivity half of [Stacks, Tag 01YB] turns. There the subsheaf
`G` is the subsheaf `F_n` of sections annihilated by `I ^ n`, taken at an exponent where the
ascending chain of those subsheaves has become constant, and the conclusion is that `F' = I ^ m F`
agrees with `F` away from the closed subscheme cut out by `I` while having no `I`-power torsion at
all. The last two results below record that specialization.

## Main results

* `AlgebraicGeometry.exists_idealPow_smul_inf_eq_bot` — the separation statement above.
* `AlgebraicGeometry.exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot` — its specialization
  to the ideal-power annihilator subsheaf of Tag 01PQ.
* `AlgebraicGeometry.exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot_of_stabilizes` — the
  conclusion the source draws: once the chain of annihilator subsheaves has become constant,
  a single ideal power of `F` meets *every* annihilator subsheaf in zero, i.e. has no
  `I`-power torsion at all.
* `AlgebraicGeometry.idealPowerAnnihilator_monotone` — the annihilator subsheaves increase with
  the exponent.

## Implementation notes

No `@[stacks 01YB]` attribute is placed here. Tag 01YB is the canonical isomorphism
`colim_n Hom(I ^ n G, F) ≅ Hom_{𝒪_U}(G|_U, F|_U)`, and these are lemmas used in proving it, not
that statement or any part of it.

Everything is phrased on the modules of sections over affine opens, which is the form in which
Artin–Rees is available (`AlgebraicGeometry.exists_ideal_pow_smul_inf_eq`) and the form in which
its consumers use it: quasi-coherent subsheaves of a quasi-coherent sheaf are determined by their
sections over affine opens, so an equality tested there is an equality of subsheaves.

The ideal power `AlgebraicGeometry.idealPower` is a least subsheaf rather than a sectionwise
power, so the containment of the sectionwise power in it needs the defining infimum property;
that is `AlgebraicGeometry.pow_sections_le_idealPower`, and it is what converts membership in the
annihilator subsheaf into annihilation by the sections of `I ^ n`. It and
`AlgebraicGeometry.smul_eq_zero_of_mem_idealPowerAnnihilator` live beside the definition of the
annihilator subsheaf, in
`StacksFrontier.AlgebraicGeometry.Properties.IdealPowerAnnihilatorQuasicoherent`, together with the
quasi-coherence of that subsheaf which the two results below now obtain by instance search
instead of as a hypothesis.

## References

* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Over every open, the `n`-th power of the ideal of sections of `I` annihilates the sections of
the ideal-power annihilator subsheaf of Tag 01PQ. -/
theorem idealPow_smul_idealPowerAnnihilator_eq_bot
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ)
    (V : X.Opens) :
    (show Ideal Γ(X, V) from I.toSubmodule.obj (op V)) ^ n •
        (show Submodule Γ(X, V) Γ(F, V) from
          (idealPowerAnnihilator I F n).toSubmodule.obj (op V)) =
      ⊥ :=
  le_antisymm
    (Submodule.smul_le.2 fun a ha s hs ↦
      (smul_eq_zero_of_mem_idealPowerAnnihilator I F n V s hs a ha) ▸ Submodule.zero_mem ⊥)
    bot_le

/-- **The Artin–Rees separation step of Stacks Project, Tag 01YB.** On a Noetherian scheme, a
quasi-coherent subsheaf `G` of a coherent sheaf `F` annihilated by `I ^ n` meets a sufficiently
high ideal multiple of `F` in zero: there is an `m` with `I ^ m F ⊓ G = 0` on every affine open.

Artin–Rees (Tag 01YA) gives a single `c` valid on all affine opens, and `m = n + c` works. -/
theorem exists_idealPow_smul_inf_eq_bot [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (G : F.Submodule) [G.toSheafOfModules.IsQuasicoherent]
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (n : ℕ)
    (hG : ∀ U : X.affineOpens,
      (show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ n •
          (show Submodule Γ(X, U.1) Γ(F, U.1) from G.toSubmodule.obj (op U.1)) =
        ⊥) :
    ∃ m : ℕ, ∀ U : X.affineOpens,
      ((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ m •
            (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          G.toSubmodule.obj (op U.1) =
        ⊥ := by
  obtain ⟨c, hc⟩ := exists_ideal_pow_smul_inf_eq F G I
  refine ⟨n + c, fun U ↦ ?_⟩
  have h := hc (n + c) (Nat.le_add_left c n) U
  rw [← h, Nat.add_sub_cancel]
  refine le_antisymm (le_trans (smul_mono_right _ inf_le_right) ?_) bot_le
  exact le_of_eq (hG U)

/-- The separation step of Tag 01YB at the ideal-power annihilator subsheaf of Tag 01PQ: on a
Noetherian scheme, if the subsheaf of sections of a coherent `F` annihilated by `I ^ n` is
quasi-coherent, then a sufficiently high ideal multiple of `F` meets it in zero. -/
theorem exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot [IsNoetherian X] (F : X.Modules)
    [F.IsCoherent] (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (n : ℕ) :
    ∃ m : ℕ, ∀ U : X.affineOpens,
      ((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ m •
            (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          (idealPowerAnnihilator I F n).toSubmodule.obj (op U.1) =
        ⊥ := by
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact exists_idealPow_smul_inf_eq_bot F (idealPowerAnnihilator I F n) I n fun U ↦
    idealPow_smul_idealPowerAnnihilator_eq_bot I F n U.1

/-- The ideal-power annihilator subsheaves of Tag 01PQ increase with the exponent: a section
annihilated by `I ^ m` is annihilated by `I ^ n` for `n ≥ m`, because the ideal powers decrease.
Stated on the sections over each open, which is the form the ascending chain argument uses. -/
theorem idealPowerAnnihilator_monotone
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) {m n : ℕ}
    (h : m ≤ n) (V : (Opens X)ᵒᵖ) :
    (idealPowerAnnihilator I F m).toSubmodule.obj V ≤
      (idealPowerAnnihilator I F n).toSubmodule.obj V := by
  intro s hs W f a ha
  exact hs W f a ((SheafOfModules.Submodule.le_iff.mp ((idealPower I).monotone h)) W ha)

/-- **The torsion-freeness conclusion of Stacks Project, Tag 01YB.** Suppose the ascending chain
of ideal-power annihilator subsheaves of a coherent `F` on a Noetherian scheme has become
constant at the exponent `n`, and that the subsheaf there is quasi-coherent. Then some ideal
multiple `I ^ m F` meets *every* annihilator subsheaf in zero: writing `F' = I ^ m F`, the
subsheaf of `F'` annihilated by `I ^ N` vanishes for every `N`, which is what the source needs
in order to replace `F` by `F'`.

For `N ≥ n` this is the hypothesis `hstab`, and for `N ≤ n` it follows from monotonicity; the
case `N = n` is `exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot`. Supplying `hstab` is the
role of the ascending chain condition, Tag 01Y8. -/
theorem exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot_of_stabilizes [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (n : ℕ)
    (hstab : ∀ N : ℕ, n ≤ N → ∀ U : X.affineOpens,
      (idealPowerAnnihilator I F N).toSubmodule.obj (op U.1) =
        (idealPowerAnnihilator I F n).toSubmodule.obj (op U.1)) :
    ∃ m : ℕ, ∀ (N : ℕ) (U : X.affineOpens),
      ((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ m •
            (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          (idealPowerAnnihilator I F N).toSubmodule.obj (op U.1) =
        ⊥ := by
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot F I n
  refine ⟨m, fun N U ↦ le_antisymm ?_ bot_le⟩
  have hle : (idealPowerAnnihilator I F N).toSubmodule.obj (op U.1) ≤
      (idealPowerAnnihilator I F n).toSubmodule.obj (op U.1) := by
    rcases le_total n N with hN | hN
    · exact le_of_eq (hstab N hN U)
    · exact idealPowerAnnihilator_monotone I F hN (op U.1)
  exact le_trans (inf_le_inf_left _ hle) (le_of_eq (hm U))

end AlgebraicGeometry
