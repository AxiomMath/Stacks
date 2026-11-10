module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.Injectivity
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
public import StacksFrontier.AlgebraicGeometry.Properties.IdealPowerAnnihilator
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Comparing the two encodings of the powers of an ideal sheaf

The tree carries two unrelated constructions of `Iⁿ` for a sheaf of ideals `I` on a scheme `X`:

* `AlgebraicGeometry.idealPower`, an order homomorphism
  `ℕᵒᵈ →o (SheafOfModules.unit X.ringCatSheaf).Submodule` defined as an infimum over *all*
  opens of `X`.  The annihilator subsheaf `AlgebraicGeometry.idealPowerAnnihilator` is stated
  in terms of it.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, the subsheaf `I ^ n • M` of a sheaf
  of modules `M`, defined as an infimum over the *affine* opens of `X` for an
  `AlgebraicGeometry.Scheme.IdealSheafData`.  This is the encoding whose sections can be
  computed, and the one the work towards Tag 01PQ uses.

Nothing related them, because the first is indexed by a submodule of the structure sheaf and the
second by ideal-sheaf data.  The passage between the two indexings is
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`; this file identifies the two
constructions along it, and then uses the identification to compute the sections of the
annihilator subsheaf over an affine open — the computation the `sInf`-over-all-opens definition
cannot supply on its own, and the one its consumers need.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPower_unitSubmodule`: **the bridge.** The
  `n`-th power of `I.unitSubmodule` in the sense of `AlgebraicGeometry.idealPower` is the
  subsheaf `I ^ n • 𝒪_X` in the sense of
  `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.obj_idealPower_affineOpen`: consequently the
  sections of `AlgebraicGeometry.idealPower I.unitSubmodule n` over an affine open `V` are
  `I(V)ⁿ`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mem_idealPowerAnnihilator_affineOpen` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerAnnihilator_obj_affineOpen`: the
  sections of `AlgebraicGeometry.idealPowerAnnihilator I.unitSubmodule F n` over an affine
  open `V` are exactly the sections of `F` over `V` annihilated by `I(V)ⁿ`.  No hypothesis on
  `F` is needed.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerAnnihilator_monotone` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow_smul_idealPowerAnnihilator_affineOpen`:
  the annihilators form an ascending chain, and `Iⁿ` kills the `n`-th one over an affine open.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_idealPowerMultiple` and
  `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent`: `I ^ n • M` is
  quasi-coherent when `M` is, and in particular `I.unitSubmodule` is quasi-coherent.  This is
  the hypothesis that the results stated for `AlgebraicGeometry.idealPower`'s encoding impose on
  their ideal, so together with the bridge it is what lets them be applied to ideal-sheaf data.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_ideal_pow_smul_inf_eq_ideal`: Artin-Rees
  (Tag 01YA) restated for ideal-sheaf data, with the ideal on an affine open spelled `I(U)`.

## Implementation notes

**The map.** `I.unitSubmodule` is `I ^ 1 • 𝒪_X`, which is what
`idealPowerMultiple_one_eq_unitSubmodule` records: the least subsheaf of `𝒪_X` containing `I(U)`
on every affine open `U` is the sheaf of ideals `I` itself, and
`Stacks.AlgebraicGeometry.IdealPowerColimit.obj_idealPow_affineOpen` computes its sections.

**The bridge.** One inequality is formal: a submodule of `𝒪_X` cutting out at least `I(V)ⁿ` on
*every* open cuts out at least `I(U)ⁿ` on every affine open, so the infimum over all opens
dominates the infimum over affine opens.  The other inequality is where the content is, and it
is locality on the affine opens: a section of the `n`-th power of `I.unitSubmodule` over an
arbitrary open `V` restricts, on each affine `V' ≤ V`, into
`(Ideal.map res (I.unitSubmodule(V)))ⁿ ≤ I(V')ⁿ`, and membership in a subsheaf is local on the
affine opens by `Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens`.  So the two
infima agree even though they are taken over different index sets.

**The annihilator over an affine open.** The membership condition defining
`AlgebraicGeometry.idealPowerAnnihilator` quantifies over every open subobject of the domain,
which is what makes it local; the price is that it says nothing concrete about any single open.
The easy half of the computation takes the identity restriction.  The other half must produce,
from `I(V)ⁿ • s = 0` over an affine `V`, the vanishing of `a • s|_W` for an arbitrary open
`W ≤ V` and an arbitrary `a` in the `n`-th power there.  That is done by restricting further to
the affine opens of `W`, where the power becomes `I(V')ⁿ = Ideal.map res (I(V)ⁿ)` by
`Stacks.AlgebraicGeometry.IdealPower.map_idealPow`, and running a span induction: a generator
`res a₀` with `a₀ ∈ I(V)ⁿ` kills `s|_{V'}` because restriction is linear and `a₀ • s = 0`.

**Two scalar actions.** A section of the structure sheaf over `W` appears both as an element of
`Γ(X, W)`, whose action on `Γ(F, W)` comes from `AlgebraicGeometry.Scheme.Modules.instModule`,
and as an element of `X.ringCatSheaf.obj.obj (op W)`, whose action comes from the `ModuleCat`
structure on `F.val.obj (op W)` and is the one appearing in
`AlgebraicGeometry.mem_idealPowerAnnihilator`.  The two are definitionally equal but not
syntactically so, so the proofs below ascribe the scalar to `Γ(X, W)` before rewriting; without
the ascription the `Γ`-level `AlgebraicGeometry.Scheme.Modules.map_smul` does not apply.  For
the same reason `idealPowerAnnihilator_obj_affineOpen` ascribes its left-hand side to
`Submodule Γ(X, V) Γ(F, V)`.

**Quasi-coherence.** `I ^ n • M` is defined as an infimum, which carries no quasi-coherence of
its own.  For quasi-coherent `M` it coincides with the subsheaf cut out by the compatible family
`U ↦ I(U) ^ n • Γ(M, U)` by
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_eq_sheafSubmodule`, and such a subsheaf
is quasi-coherent by `Stacks.AlgebraicGeometry.GabberColimit.isQuasicoherent_sheafSubmodule`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA) (Artin-Rees, restated
  here for ideal-sheaf data; it is proved in
  `StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/ArtinRees.lean`)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.GabberColimit
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-- The structure sheaf `𝒪_X`, as a sheaf of modules over itself, is quasi-coherent. -/
local instance instIsQuasicoherentStructureModule' (X : Scheme.{u}) :
    (structureModule X).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X

/-! ### Ideal-sheaf data as a submodule of the structure sheaf -/

/-- The first ideal power of the structure sheaf is the ideal sheaf itself: both have `I(U)` as
sections over every affine open, so the affine-local comparison identifies them. -/
theorem idealPowerMultiple_one_eq_unitSubmodule (I : X.IdealSheafData) :
    idealPowerMultiple I 1 (structureModule X) = I.unitSubmodule :=
  AlgebraicGeometry.Scheme.Modules.submodule_eq_of_obj_affineOpens_eq _ _ fun V => by
    rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple I 1
        (structureModule X) V, pow_one, I.unitSubmodule_obj_affine V]
    change (I.ideal V) • (⊤ : Ideal Γ(X, V.1)) = _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-! ### The bridge -/

/-- **The two encodings of `Iⁿ` agree.** The `n`-th power of the ideal subsheaf attached to
ideal-sheaf data `I`, formed as the infimum over *all* opens of `X` of the subsheaves containing
the sectionwise powers, is the subsheaf `I ^ n • 𝒪_X` formed as the infimum over the *affine*
opens.

The nontrivial inequality is that the infimum over the affine opens already satisfies the
condition imposed at every open, which holds because membership in a subsheaf is local on the
affine opens. -/
theorem idealPower_unitSubmodule (I : X.IdealSheafData) (n : ℕ) :
    AlgebraicGeometry.idealPower I.unitSubmodule n
      = idealPowerMultiple I n (structureModule X) := by
  refine le_antisymm (sInf_le ?_) ?_
  · intro V
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = V := ⟨V.unop, rfl⟩
    intro a ha
    obtain ⟨a, rfl⟩ : ∃ b : Γ(X, W), b = a := ⟨a, rfl⟩
    refine mem_of_forall_affineOpens (M := structureModule X) _
      (show Γ(structureModule X, W) from a) fun V' hV' ↦ ?_
    rw [obj_idealPow_affineOpen I n V']
    have hle : Ideal.map (X.presheaf.map (homOfLE hV').op).hom
        (show Ideal Γ(X, W) from I.unitSubmodule.toSubmodule.obj (op W)) ≤ I.ideal V' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h2 := I.unitSubmodule.toSubmodule.map (homOfLE hV').op hx
      rwa [AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine] at h2
    have h1 : (X.presheaf.map (homOfLE hV').op).hom a ∈
        Ideal.map (X.presheaf.map (homOfLE hV').op).hom
          ((show Ideal Γ(X, W) from I.unitSubmodule.toSubmodule.obj (op W)) ^ n) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h1
    exact pow_le_pow_left' hle n h1
  · rw [idealPowerMultiple_le_iff]
    intro U
    change _ ≤ (sInf ((fun P : (structureModule X).Submodule => P.toSubmodule) ''
      { K : (structureModule X).Submodule | ∀ V : (Opens X)ᵒᵖ,
        (show Ideal _ from I.unitSubmodule.toSubmodule.obj V) ^ n
          ≤ K.toSubmodule.obj V })).obj (op U.1)
    rw [PresheafOfModules.Submodule.sInf_obj]
    refine le_iInf₂ fun P hP ↦ ?_
    obtain ⟨Q, hQ, rfl⟩ := hP
    have h3 := hQ (op U.1)
    rw [AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine] at h3
    change (I.ideal U ^ n) • (⊤ : Ideal Γ(X, U.1)) ≤ _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact h3

/-- The sections of the `n`-th power of `I.unitSubmodule`, in the sense of
`AlgebraicGeometry.idealPower`, over an affine open `V` are `I(V)ⁿ`. -/
theorem obj_idealPower_affineOpen (I : X.IdealSheafData) (n : ℕ) (V : X.affineOpens) :
    (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.obj (op V.1)
      = (I.ideal V ^ n : Ideal Γ(X, V.1)) := by
  rw [idealPower_unitSubmodule I n]
  exact obj_idealPow_affineOpen I n V

/-- A section of the `n`-th power of `I.unitSubmodule` over an open `W` restricts, on an affine
open `V ≤ W`, into `I(V)ⁿ`. -/
theorem res_mem_idealPower (I : X.IdealSheafData) (n : ℕ) {W : X.Opens} (V : X.affineOpens)
    (hV : V.1 ≤ W) {a : Γ(X, W)}
    (ha : a ∈ (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.obj (op W)) :
    X.presheaf.map (homOfLE hV).op a ∈ (I.ideal V ^ n : Ideal Γ(X, V.1)) := by
  have h := (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.map
    (homOfLE hV).op ha
  rwa [obj_idealPower_affineOpen] at h

/-! ### The annihilator subsheaf over an affine open -/

/-- **The sections of the ideal-power annihilator over an affine open.** A section of `F` over an
affine open `V` lies in `AlgebraicGeometry.idealPowerAnnihilator I.unitSubmodule F n` exactly
when it is annihilated by `I(V)ⁿ`.

The defining condition quantifies over all open subobjects of `V`; this reduces it to a single
condition over `V` itself.  No quasi-coherence or finiteness hypothesis on `F` is used. -/
theorem mem_idealPowerAnnihilator_affineOpen (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (V : X.affineOpens) (s : Γ(F, V.1)) :
    s ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op V.1) ↔
      ∀ a ∈ (I.ideal V ^ n : Ideal Γ(X, V.1)), a • s = 0 := by
  refine (mem_idealPowerAnnihilator I.unitSubmodule F n s).trans ?_
  constructor
  · intro h a ha
    have hmem : a ∈ (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.obj
        (op V.1) := by rw [obj_idealPower_affineOpen]; exact ha
    have hz : a • F.presheaf.map (homOfLE (le_refl V.1)).op s = 0 :=
      h (op V.1) (homOfLE (le_refl V.1)).op a hmem
    rwa [res_self F s] at hz
  · intro h W f a ha
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = W := ⟨W.unop, rfl⟩
    obtain ⟨a, rfl⟩ : ∃ b : Γ(X, W), b = a := ⟨a, rfl⟩
    have hWV : W ≤ V.1 := f.unop.le
    change a • F.presheaf.map (homOfLE hWV).op s = (0 : Γ(F, W))
    refine eq_zero_of_restrict_affineOpens_eq_zero (M := F)
      (a • F.presheaf.map (homOfLE hWV).op s) fun V' hV' ↦ ?_
    have hV'V : V'.1 ≤ V.1 := hV'.trans hWV
    have key : ∀ b ∈ (I.ideal V' ^ n : Ideal Γ(X, V'.1)),
        b • F.presheaf.map (homOfLE hV'V).op s = 0 := by
      intro b hbm
      rw [← map_idealPow I n hV'V, Ideal.map] at hbm
      induction hbm using Submodule.span_induction with
      | mem c hc =>
        obtain ⟨a₀, ha₀, rfl⟩ := hc
        rw [← F.map_smul (homOfLE hV'V) a₀ s, h a₀ ha₀, map_zero]
      | zero => rw [zero_smul]
      | add p q _ _ hp hq => rw [add_smul, hp, hq, add_zero]
      | smul r p _ hp => rw [smul_eq_mul, mul_smul, hp, smul_zero]
    rw [F.map_smul (homOfLE hV') a (F.presheaf.map (homOfLE hWV).op s), res_res F hWV hV' s]
    exact key _ (res_mem_idealPower I n V' hV' ha)

/-- The ideal-power annihilator over an affine open `V` is the `I(V)ⁿ`-torsion submodule of
`Γ(F, V)`. -/
theorem idealPowerAnnihilator_obj_affineOpen (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (V : X.affineOpens) :
    (show Submodule Γ(X, V.1) Γ(F, V.1) from
        (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op V.1))
      = Submodule.torsionBySet Γ(X, V.1) Γ(F, V.1)
          ((I.ideal V ^ n : Ideal Γ(X, V.1)) : Set Γ(X, V.1)) := by
  refine SetLike.ext fun s ↦ ?_
  obtain ⟨s, rfl⟩ : ∃ t : Γ(F, V.1), t = s := ⟨s, rfl⟩
  refine ((mem_idealPowerAnnihilator_affineOpen I F n V s).trans ?_).trans
    (Submodule.mem_torsionBySet_iff _ _).symm
  exact ⟨fun h a ↦ h a.1 a.2, fun h a ha ↦ h ⟨a, ha⟩⟩

/-- The ideal-power annihilators increase with the exponent: a section annihilated by `Iⁿ` is
annihilated by `I^m` for `m ≥ n`, because `I^m ≤ Iⁿ`.

This is the ascending chain whose stabilization Tag 01Y8 provides. -/
theorem idealPowerAnnihilator_monotone
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    idealPowerAnnihilator I F n ≤ idealPowerAnnihilator I F m := by
  have hle : AlgebraicGeometry.idealPower I m ≤ AlgebraicGeometry.idealPower I n :=
    (AlgebraicGeometry.idealPower I).monotone (a := m) (b := n) h
  intro V s hs W f a ha
  exact hs W f a (SheafOfModules.Submodule.le_iff.mp hle W ha)

/-- Over an affine open, `Iⁿ` annihilates the sections annihilated by `Iⁿ`; that is, the product
of `I(V)ⁿ` with the sections of the annihilator over `V` is zero.

This is the step of Tag 01YB that makes the Artin-Rees intersection vanish. -/
theorem idealPow_smul_idealPowerAnnihilator_affineOpen (I : X.IdealSheafData) (F : X.Modules)
    (n : ℕ) (V : X.affineOpens) :
    (I.ideal V ^ n : Ideal Γ(X, V.1)) •
        (show Submodule Γ(X, V.1) Γ(F, V.1) from
          (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op V.1)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha s hs ↦ ?_) bot_le
  obtain ⟨s, rfl⟩ : ∃ t : Γ(F, V.1), t = s := ⟨s, rfl⟩
  rw [Submodule.mem_bot]
  exact (mem_idealPowerAnnihilator_affineOpen I F n V s).mp hs a ha

/-! ### Quasi-coherence, and Artin-Rees for ideal-sheaf data -/

/-- The subsheaf `I ^ n • M` of a quasi-coherent sheaf of modules is quasi-coherent. -/
instance isQuasicoherent_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] :
    (idealPowerMultiple I n M).toSheafOfModules.IsQuasicoherent := by
  rw [idealPowerMultiple_eq_sheafSubmodule I n M]
  exact isQuasicoherent_sheafSubmodule M (idealPowSections I n M)
    (isCompatible_idealPowSections I n M)

/-- **Artin-Rees for ideal-sheaf data.** For a coherent sheaf `F` on a Noetherian scheme, a
quasi-coherent subsheaf `G` and ideal-sheaf data `I`, there is a single constant `c` such that
`I^(n-c) • (Iᶜ F ∩ G) = Iⁿ F ∩ G` on every affine open, for all `n ≥ c`.

This is `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq` (Tag 01YA), whose ideal is a submodule
of the structure sheaf, transported along `unitSubmodule` so that the ideal appearing on an
affine open is `I(U)` rather than an infimum over all opens.  Both the quasi-coherence
hypothesis on the ideal and the affine computation come from this file. -/
theorem exists_ideal_pow_smul_inf_eq_ideal [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (G : F.Submodule) [G.toSheafOfModules.IsQuasicoherent] (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ U : X.affineOpens,
      I.ideal U ^ (n - c) • ((I.ideal U ^ c • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          G.toSubmodule.obj (op U.1)) =
        (I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓ G.toSubmodule.obj (op U.1) := by
  obtain ⟨c, hc⟩ := exists_ideal_pow_smul_inf_eq F G I.unitSubmodule
  refine ⟨c, fun n hn U ↦ ?_⟩
  have h := hc n hn U
  rwa [AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine I U] at h

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
