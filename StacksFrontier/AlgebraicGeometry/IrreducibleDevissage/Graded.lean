module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Splicing
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Cokernel
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Splitting
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# Step 3 of [Stacks, Tag 01YF] discharged, and [Stacks, Tag 01YG] on step 4 alone

In this repository [Stacks, Tag 01YG] rests on the single hypothesis
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` — the irreducible case of
[Stacks, Tag 01YF] — through
`Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage`, 01YD having been
discharged unconditionally. The source proves that irreducible case in two steps. **Step 3**
filters a coherent module `F` whose support is irreducible by the powers of the ideal sheaf `J` of
the reduced induced structure on `supp F`; the filtration is finite by [Stacks, Tag 01Y9] and its
graded pieces are annihilated by `J`. **Step 4** is [Stacks, Tag 01YE], which treats a module so
annihilated.

**This file discharges step 3 unconditionally**, so 01YG rests on step 4 alone:
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissage`.

## Main definitions

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep`: the inclusion
  `J ^ (n + 1) • F ⟶ J ^ n • F`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissage`: **step 4 of the proof
  of [Stacks, Tag 01YF], as a hypothesis** — a coherent quasi-coherent module annihilated by the
  ideal sheaf of an irreducible closed set `Z` carries a bounded dévissage filtration whose
  successive quotients are direct images of quasi-coherent ideal sheaves on integral closed
  subschemes or are supported strictly inside `Z`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissageIn`: the same with the
  subscheme confined to `Z`, which is what [Stacks, Tag 01YH] consumes.

## Main results

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.smul_top_cokernel_idealPowStep`: **the graded
  pieces of the ideal-adic filtration are annihilated by the ideal.**
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.isIso_idealPowSmulHom_zero`: `J ^ 0 • F` is `F`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_of_killed`: **step 3 of the
  proof of [Stacks, Tag 01YF], for an arbitrary quotient class** — a coherent quasi-coherent
  module supported in a closed set carries a dévissage filtration with quotients in `Q` as soon
  as every module annihilated by the ideal of that set does.
* `hasIrreducibleDevissage_of_hasKilledIdealDevissage` and
  `hasIrreducibleDevissageIn_of_hasKilledIdealDevissageIn`: **the irreducible case of
  [Stacks, Tag 01YF], absolute and relativized, from step 4 alone.**
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.property_of_hasKilledIdealDevissage`:
  **the statement of Tag 01YG verbatim with `HasKilledIdealDevissage X` as its one added
  hypothesis.**

## Implementation notes

**The right-exactness this needs is available.** That
the graded pieces are annihilated by `J` needs
right-exactness of `Γ(-, U)` for quasi-coherent modules over an affine open.
`StacksFrontier/AlgebraicGeometry/SectionsExact/Basic.lean` supplies only the
left-exact half, but right-exactness is proved elsewhere, as
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`
(`StacksFrontier/AlgebraicGeometry/SectionEpiAffine/Basic.lean:147`), deliberately untagged: an
epimorphism of quasi-coherent modules is surjective on sections over an affine open. With it the
graded-piece statement is `smul_top_cokernel_idealPowStep` and needs nothing new. Concretely, a
section `q` of `J ^ n • F / J ^ (n + 1) • F` over an affine `U` lifts to a section `a` of
`J ^ n • F`, whose underlying section `s` of `F` lies in `J(U) ^ n • Γ(F, U)` by
`Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul`; then `r • s` lies in
`J(U) ^ (n + 1) • Γ(F, U)` for `r ∈ J(U)`, so `r • a` is in the image of the step map and
`r • q = 0`.

**Why step 3 is formulated through a hypothesis on the graded pieces and not through a submodule
of `F`.** The predecessor of this file reduced `HasIrreducibleDevissage` to
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasGenericIdealSub`: one coherent submodule
`G ⊆ F` filtered by ideal pushforwards **alone**, with `supp (cokernel ι) ⊂ supp F`. That is a
sufficient condition but not the source's step 4, and it is strictly harder: forbidding
small-support quotients inside the filtration of `G` means the ideal-pushforward refinement must
already be available for every graded piece of the ideal-adic filtration, which is the
Noetherian induction of 01YF itself, and so is not available at this point of the proof. By
contrast `HasKilledIdealDevissage` is exactly what [Stacks, Tag 01YE] plus the filtration of
`i_*(I ^ {⊕ r})` by its `r` factors delivers, and nothing more: annihilation by `J` already
forces the support into `Z`, so no support hypothesis is carried.

**Step 3 does not see the quotient class.** `hasDevissageWith_of_killed` takes the class as a
parameter and uses nothing about it but invariance under isomorphism, and it does not use the
irreducibility of `Z` either; both enter only through the step-4 hypothesis. So the one proof
serves `Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`, which Tag 01YG
needs, and `Stacks.AlgebraicGeometry.ConfinedDevissage.HasIrreducibleDevissageIn`, the confined
form Tag 01YH needs and which is strictly stronger.

**Annihilation is read affine-locally.** `HasKilledIdealDevissage` states it as
`J(U) • Γ(Q, U) = ⊥` for every affine open `U`, which is the form both its producer and its
consumer want: `Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul` computes exactly such
sections, and [Stacks, Tag 087T] — a module killed by `J` is a direct image from the closed
subscheme — is itself an affine-local statement.

**No `@[stacks]` attribute is attached.** Tag 01YG is a single unlabelled assertion, and
every theorem below either carries `HasKilledIdealDevissage X`, which the tag does not have, or
is a fragment. 01YE, 01YF, 01YG and 01YH are not proved here.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Opposite
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded
open Stacks.AlgebraicGeometry.GabberColimit

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The zeroth step of the filtration is everything -/

/-- At exponent zero the family defining `I ^ n • F` is all of the sections. -/
theorem idealPowFamily_zero (I : X.IdealSheafData) (F : X.Modules) (U : X.affineOpens) :
    IdealPowerSmul.idealPowFamily I 0 F U = ⊤ := by
  rw [show IdealPowerSmul.idealPowFamily I 0 F U =
    I.ideal U ^ 0 • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) from rfl, pow_zero, Ideal.one_eq_top,
    Submodule.top_smul]

/-- Every section lies locally in the family defining `I ^ 0 • F`. -/
theorem isLocallyIn_idealPowFamily_zero (I : X.IdealSheafData) (F : X.Modules) {V : X.Opens}
    (s : Γ(F, V)) : IsLocallyIn F (IdealPowerSmul.idealPowFamily I 0 F) s := by
  intro W hW
  rw [idealPowFamily_zero]
  exact Submodule.mem_top

/-- The inclusion `I ^ 0 • F ⟶ F` is an epimorphism: it is surjective on sections over every
open, since every section of `F` lies locally in the family defining `I ^ 0 • F`. -/
theorem epi_idealPowSmulHom_zero (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    Epi (IdealPowerSmul.idealPowSmulHom I 0 F) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro W g hg
  refine Scheme.Modules.hom_ext g 0 fun V => ?_
  ext s
  have h1 : (IdealPowerSmul.idealPowSmulHom I 0 F).app V
      (mkSection F (IdealPowerSmul.idealPowFamily I 0 F)
        (IdealPowerSmul.isCompatible_idealPowFamily I 0 F) s
        (isLocallyIn_idealPowFamily_zero I F s)) = s :=
    IdealPowerSmul.idealPowSmulHom_app_mkSection I 0 F s (isLocallyIn_idealPowFamily_zero I F s)
  have h2 : (IdealPowerSmul.idealPowSmulHom I 0 F ≫ g).app V
      (mkSection F (IdealPowerSmul.idealPowFamily I 0 F)
        (IdealPowerSmul.isCompatible_idealPowFamily I 0 F) s
        (isLocallyIn_idealPowFamily_zero I F s)) = 0 := by
    rw [hg]
    rfl
  exact h1 ▸ h2

/-- **`I ^ 0 • F` is `F`.** -/
theorem isIso_idealPowSmulHom_zero (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (IdealPowerSmul.idealPowSmulHom I 0 F) :=
  have : Epi (IdealPowerSmul.idealPowSmulHom I 0 F) := epi_idealPowSmulHom_zero I F
  have : Mono (IdealPowerSmul.idealPowSmulHom I 0 F) :=
    inferInstanceAs (Mono (IdealPowerSmul.idealPowSmul I 0 F).ι)
  isIso_of_mono_of_epi _

/-! ### The ideal-adic filtration -/

/-- A zero module carries the empty filtration, whatever the quotient class. -/
theorem hasDevissageWith_of_isZero {Q : X.Modules → Prop} {F : X.Modules} (hF : IsZero F) :
    HasDevissageWith Q F :=
  ⟨0, fun _ => F, fun _ => 𝟙 F, by omega, hF, fun _ _ => isCoherent_of_isZero hF, by omega,
    ⟨Iso.refl F⟩, by omega⟩

/-- The ideal-power filtration is decreasing. -/
theorem idealPowSmul_antitone (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    {n m : ℕ} (h : n ≤ m) : IdealPowerSmul.idealPowSmul I m F ≤ IdealPowerSmul.idealPowSmul I n
      F := by
  rw [SheafOfModules.Submodule.le_iff, PresheafOfModules.Submodule.le_iff]
  intro V s hs W hW
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hs W hW)

/-- The inclusion between two comparable submodules of a sheaf of modules is a monomorphism,
since composing it with the inclusion of the larger one gives the inclusion of the smaller. -/
theorem mono_homOfLE {M : X.Modules} {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    Mono (SheafOfModules.Submodule.homOfLE hle) :=
  mono_of_mono_fac (SheafOfModules.Submodule.homOfLE_ι hle)

/-- One step `I ^ (n + 1) • F ⟶ I ^ n • F` of the ideal-adic filtration. -/
def idealPowStep (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IdealPowerSmul.idealPowSmulModule I (n + 1) F ⟶ IdealPowerSmul.idealPowSmulModule I n F :=
  SheafOfModules.Submodule.homOfLE (idealPowSmul_antitone I F (Nat.le_succ n))

/-- The step map followed by the inclusion of `I ^ n • F` into `F` is the inclusion of
`I ^ (n + 1) • F` into `F`. -/
theorem idealPowStep_comp_hom (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) : idealPowStep I F n ≫ IdealPowerSmul.idealPowSmulHom I n F =
      IdealPowerSmul.idealPowSmulHom I (n + 1) F :=
  SheafOfModules.Submodule.homOfLE_ι _

/-- The step `I ^ (n + 1) • F ⟶ I ^ n • F` of the ideal-adic filtration is a monomorphism. -/
instance mono_idealPowStep (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Mono (idealPowStep I F n) :=
  have : Mono (IdealPowerSmul.idealPowSmulHom I (n + 1) F) :=
    inferInstanceAs (Mono (IdealPowerSmul.idealPowSmul I (n + 1) F).ι)
  mono_of_mono_fac (idealPowStep_comp_hom I F n)

/-- The cokernel of a step of the ideal-adic filtration is coherent and quasi-coherent. -/
private theorem isCoherent_and_isQuasicoherent_cokernel_idealPowStep [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (n : ℕ) :
    (cokernel (idealPowStep I F n)).IsCoherent ∧
      (cokernel (idealPowStep I F n)).IsQuasicoherent :=
  have : (cokernel (idealPowStep I F n)).IsCoherent :=
    isCoherent_cokernel' _ (IdealPowerSmul.isCoherent_idealPowSmul I (n + 1) F)
      (IdealPowerSmul.isCoherent_idealPowSmul I n F)
  ⟨this, isQuasicoherent_of_isCoherent _⟩

/-- **The successive quotient of the ideal-adic filtration is killed by the ideal, over a locally
Noetherian scheme.** On an affine open the sections of the quotient are a quotient of the sections
of `I ^ n • F`, by `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` — the right-exactness
of `Γ(-, U)` on quasi-coherent modules over an affine open — and `I(U)` carries
`I(U) ^ n • Γ(F, U)` into `I(U) ^ (n + 1) • Γ(F, U)`, which is exactly the submodule being divided
out. -/
theorem smul_top_cokernel_idealPowStep_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsCoherent] (n : ℕ) (U : X.affineOpens) :
    I.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(cokernel (idealPowStep I F n), U.1)) = ⊥ := by
  have hAq : (IdealPowerSmul.idealPowSmulModule I n F).IsQuasicoherent :=
    IdealPowerSmul.isQuasicoherent_idealPowSmul I n F
  obtain ⟨hCc, hCq⟩ := isCoherent_and_isQuasicoherent_cokernel_idealPowStep I F n
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun r hr q _ => ?_
  rw [Submodule.mem_bot]
  have hsurj : Function.Surjective
      ((cokernel.π (idealPowStep I F n)).app U.1 :
        Γ(IdealPowerSmul.idealPowSmulModule I n F, U.1) → Γ(cokernel (idealPowStep I F n), U.1)) :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (idealPowStep I F n)) U.1 U.2
  obtain ⟨a, ha⟩ := hsurj q
  obtain ⟨s, hs⟩ : ∃ s : Γ(F, U.1), (IdealPowerSmul.idealPowSmulHom I n F).app U.1 a = s := ⟨_, rfl⟩
  have hsloc : IsLocallyIn F (IdealPowerSmul.idealPowFamily I n F) s := by
    rw [← hs]
    exact isLocallyIn_valSection F _ (IdealPowerSmul.isCompatible_idealPowFamily I n F) a
  have hsmem : s ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) :=
    (isLocallyIn_iff_mem F _ (IdealPowerSmul.isCompatible_idealPowFamily I n F) U s).mp hsloc
  have hrsmem : r • s ∈ IdealPowerSmul.idealPowFamily I (n + 1) F U := by
    change r • s ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr hsmem
  have hrsloc : IsLocallyIn F (IdealPowerSmul.idealPowFamily I (n + 1) F) (r • s) :=
    (isLocallyIn_iff_mem F _ (IdealPowerSmul.isCompatible_idealPowFamily I (n + 1) F) U (r • s)).mpr
      hrsmem
  set b : Γ(IdealPowerSmul.idealPowSmulModule I (n + 1) F, U.1) :=
    mkSection F (IdealPowerSmul.idealPowFamily I (n + 1) F)
      (IdealPowerSmul.isCompatible_idealPowFamily I (n + 1) F) (r • s) hrsloc with hb
  have hcomp : (IdealPowerSmul.idealPowSmulHom I n F).app U.1 ((idealPowStep I F n).app U.1 b) =
      (IdealPowerSmul.idealPowSmulHom I (n + 1) F).app U.1 b := by
    have h0 := congrArg
      (fun φ : IdealPowerSmul.idealPowSmulModule I (n + 1) F ⟶ F => Scheme.Modules.Hom.app φ U.1 b)
      (idealPowStep_comp_hom I F n)
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h0
  have hstep : (idealPowStep I F n).app U.1 b = r • a := by
    refine valSection_inj F _ (IdealPowerSmul.isCompatible_idealPowFamily I n F) ?_
    change (IdealPowerSmul.idealPowSmulHom I n F).app U.1 ((idealPowStep I F n).app U.1 b) =
      (IdealPowerSmul.idealPowSmulHom I n F).app U.1 (r • a)
    rw [hcomp, hb, IdealPowerSmul.idealPowSmulHom_app_mkSection I (n + 1) F (r • s) hrsloc,
      Scheme.Modules.Hom.app_smul, hs]
  have hzero : (cokernel.π (idealPowStep I F n)).app U.1
      ((idealPowStep I F n).app U.1 b) = 0 := by
    have h0 : ((idealPowStep I F n) ≫ cokernel.π (idealPowStep I F n)).app U.1 b =
        (0 : IdealPowerSmul.idealPowSmulModule I (n + 1) F ⟶
          cokernel (idealPowStep I F n)).app U.1 b :=
      congrArg
        (fun φ : IdealPowerSmul.idealPowSmulModule I (n + 1) F ⟶ cokernel (idealPowStep I F n) =>
          Scheme.Modules.Hom.app φ U.1 b) (cokernel.condition (idealPowStep I F n))
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h0
    rw [h0]
    simp
  rw [hstep, Scheme.Modules.Hom.app_smul, ha] at hzero
  exact hzero

/-- **The successive quotient of the ideal-adic filtration is killed by the ideal.** On an affine
open the sections of the quotient are a quotient of the sections of `I ^ n • F`, by
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` — the right-exactness of `Γ(-, U)` on
quasi-coherent modules over an affine open — and `I(U)` carries `I(U) ^ n • Γ(F, U)` into
`I(U) ^ (n + 1) • Γ(F, U)`, which is exactly the submodule being divided out. -/
theorem smul_top_cokernel_idealPowStep [IsNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsCoherent] (n : ℕ) (U : X.affineOpens) :
    I.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(cokernel (idealPowStep I F n), U.1)) = ⊥ :=
  smul_top_cokernel_idealPowStep_of_isLocallyNoetherian I F n U

/-! ### Step 4 as a hypothesis, and the reduction to it -/

/-- The quotient class of `HasIrreducibleDevissage`, relative to an arbitrary set, is invariant
under isomorphism. -/
theorem isIdealPushforward_or_supp_ssubset_of_iso' {S : Set X} {M N : X.Modules} (e : M ≅ N)
    (h : IsIdealPushforward M ∨ SheafOfModules.supp M ⊂ S) :
    IsIdealPushforward N ∨ SheafOfModules.supp N ⊂ S := by
  rcases h with h | h
  · exact Or.inl (isIdealPushforward_of_iso e h)
  · exact Or.inr (by rwa [← supp_eq_of_iso e])

/-- The confined quotient class of [Stacks, Tag 01YH] is invariant under isomorphism. -/
theorem isIdealPushforwardIn_of_iso {W : Set X} {M N : X.Modules} (e : M ≅ N)
    (h : ConfinedDevissage.IsIdealPushforwardIn W M) : ConfinedDevissage.IsIdealPushforwardIn W
      N := by
  obtain ⟨Z, i, hi, hZ, I, hI, hr, ⟨f⟩⟩ := h
  exact ⟨Z, i, hi, hZ, I, hI, hr, ⟨e.symm.trans f⟩⟩

/-- The mixed quotient class of [Stacks, Tag 01YH] is invariant under isomorphism. -/
theorem isIdealPushforwardIn_or_supp_ssubset_of_iso {W S : Set X} {M N : X.Modules} (e : M ≅ N)
    (h : ConfinedDevissage.IsIdealPushforwardIn W M ∨ SheafOfModules.supp M ⊂ S) :
    ConfinedDevissage.IsIdealPushforwardIn W N ∨ SheafOfModules.supp N ⊂ S := by
  rcases h with h | h
  · exact Or.inl (isIdealPushforwardIn_of_iso e h)
  · exact Or.inr (by rwa [← supp_eq_of_iso e])

/-- **The ideal-adic filtration, spliced.** Every term of the filtration
`0 = J ^ n • F ⊆ … ⊆ J ^ 1 • F ⊆ J ^ 0 • F` carries a dévissage filtration with quotients in `Q`,
by downward induction: the bottom term is zero, and each step splices the filtration of
`J ^ (m + 1) • F` with the one `hkilled` supplies for the successive quotient, which
`smul_top_cokernel_idealPowStep` shows is annihilated by `J`.

Neither the irreducibility of `Z` nor any property of `Q` beyond invariance under isomorphism is
used; both enter only through `hkilled`. -/
theorem hasDevissageWith_idealPowSmul [IsNoetherian X] (Z : Closeds X) (Q : X.Modules → Prop)
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    (hkilled : ∀ M : X.Modules, M.IsQuasicoherent → M.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) = ⊥) → HasDevissageWith Q M)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (n : ℕ)
    (hn : IsZero (IdealPowerSmul.idealPowSmul (IdealPowerSmul.closedIdeal Z) n F).toSheafOfModules)
      :
    ∀ j : ℕ, HasDevissageWith Q
      (IdealPowerSmul.idealPowSmul (IdealPowerSmul.closedIdeal Z) (n - j) F).toSheafOfModules := by
  intro j
  induction j with
  | zero => simpa using hasDevissageWith_of_isZero hn
  | succ j IH =>
    by_cases hjn : n ≤ j
    · have h1 : n - j = 0 := by omega
      have h2 : n - (j + 1) = 0 := by omega
      rw [h2]
      rw [h1] at IH
      exact IH
    · have hm : n - j = (n - (j + 1)) + 1 := by omega
      rw [hm] at IH
      set m := n - (j + 1) with hmdef
      obtain ⟨hCc, hCq⟩ :=
        isCoherent_and_isQuasicoherent_cokernel_idealPowStep (IdealPowerSmul.closedIdeal Z) F m
      have hAc :
        (IdealPowerSmul.idealPowSmulModule (IdealPowerSmul.closedIdeal Z) m F).IsCoherent :=
        IdealPowerSmul.isCoherent_idealPowSmul _ m F
      have hmono : Mono (idealPowStep (IdealPowerSmul.closedIdeal Z) F m) :=
        mono_idealPowStep (IdealPowerSmul.closedIdeal Z) F m
      exact @hasDevissageWith_trans' X _ hQ _ _
        (idealPowStep (IdealPowerSmul.closedIdeal Z) F m) hmono hAc IH
        (hkilled _ hCq hCc (smul_top_cokernel_idealPowStep (IdealPowerSmul.closedIdeal Z) F m))

/-- **Step 3 of the proof of [Stacks, Tag 01YF], for an arbitrary quotient class.** A coherent
quasi-coherent module supported in a closed set `Z` carries a bounded dévissage filtration with
quotients in `Q`, as soon as every coherent quasi-coherent module annihilated by the ideal sheaf
of `Z` does.

The filtration is the ideal-adic one; it is finite by [Stacks, Tag 01Y9]
(`exists_isZero_idealPowSmul`), its graded pieces are annihilated by that ideal
(`smul_top_cokernel_idealPowStep`), and `J ^ 0 • F` is `F`
(`isIso_idealPowSmulHom_zero`). -/
theorem hasDevissageWith_of_killed [IsNoetherian X] (Z : Closeds X) (Q : X.Modules → Prop)
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    (hkilled : ∀ M : X.Modules, M.IsQuasicoherent → M.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) = ⊥) → HasDevissageWith Q M)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (hsupp : SheafOfModules.supp F ⊆ (Z : Set X)) : HasDevissageWith Q F := by
  obtain ⟨n, hn⟩ := exists_isZero_idealPowSmul F Z hsupp
  have key := hasDevissageWith_idealPowSmul Z Q hQ hkilled F n hn n
  rw [Nat.sub_self] at key
  have : IsIso (IdealPowerSmul.idealPowSmulHom (IdealPowerSmul.closedIdeal Z) 0 F) :=
    isIso_idealPowSmulHom_zero (IdealPowerSmul.closedIdeal Z) F
  exact hasDevissageWith_of_iso
    (asIso (IdealPowerSmul.idealPowSmulHom (IdealPowerSmul.closedIdeal Z) 0 F)) key

/-- **Step 4 of the proof of [Stacks, Tag 01YF], as a hypothesis.** A coherent quasi-coherent
module annihilated by the ideal sheaf of an irreducible closed set `Z` carries a bounded
dévissage filtration each of whose successive quotients is either the direct image of a
quasi-coherent ideal sheaf on an integral closed subscheme, or supported strictly inside `Z`.

Annihilation is read affine-locally: `J(U)` kills every section over every affine open `U`. This
is the hypothesis of [Stacks, Tag 01YE] — which, through [Stacks, Tag 087T], turns such a module
into the direct image `i_* G` of a coherent module on the integral closed subscheme `Z`, produces
a monomorphism `i_*(I ^ {⊕ r}) ⟶ i_* G` that is an isomorphism near the generic point of `Z`, and
so leaves a cokernel supported strictly inside `Z` — together with the filtration of
`i_*(I ^ {⊕ r})` by its `r` factors. -/
def HasKilledIdealDevissage (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      HasDevissageWith
        (fun M => IsIdealPushforward M ∨ SheafOfModules.supp M ⊂ (Z : Set X)) Q

/-- **Step 4 of the proof of [Stacks, Tag 01YF], as a hypothesis, with the subscheme confined to
`Z`.** This is `HasKilledIdealDevissage` with the containment the source's construction actually
delivers — step 4 takes the subscheme to be the reduced induced structure on `Z` — and it is
what [Stacks, Tag 01YH] consumes, through
`Stacks.AlgebraicGeometry.ConfinedDevissage.HasIrreducibleDevissageIn`. -/
def HasKilledIdealDevissageIn (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      HasDevissageWith
        (fun M => ConfinedDevissage.IsIdealPushforwardIn (Z : Set X) M ∨
          SheafOfModules.supp M ⊂ (Z : Set X)) Q

/-- **The irreducible case of [Stacks, Tag 01YF] from step 4 of its proof alone.** Step 3 — the
ideal-adic filtration of a coherent module with irreducible support, and the fact that its graded
pieces are annihilated by the ideal of the support — is discharged here unconditionally.

Composed with `Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage` this gives
the statement of Tag 01YG verbatim with `HasKilledIdealDevissage X` as its one added hypothesis. -/
theorem hasIrreducibleDevissage_of_hasKilledIdealDevissage [IsNoetherian X]
    (h : HasKilledIdealDevissage X) : DevissageNoetherian.HasIrreducibleDevissage X := by
  intro F hF hirr
  have hFc : F.IsCoherent := hF
  have hFq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact hasDevissageWith_of_killed
    ⟨SheafOfModules.supp F, DevissageNoetherian.forall_isClosed_supp X F hF⟩ _
    isIdealPushforward_or_supp_ssubset_of_iso'
    (h ⟨SheafOfModules.supp F, DevissageNoetherian.forall_isClosed_supp X F hF⟩ hirr) F subset_rfl

/-- **The relativized irreducible case of [Stacks, Tag 01YF] from step 4 alone.** The same
reduction for the confined quotient class that [Stacks, Tag 01YH] needs: step 3 is independent of
the class, so discharging it once serves both
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` and
`Stacks.AlgebraicGeometry.ConfinedDevissage.HasIrreducibleDevissageIn`. -/
theorem hasIrreducibleDevissageIn_of_hasKilledIdealDevissageIn [IsNoetherian X]
    (h : HasKilledIdealDevissageIn X) : ConfinedDevissage.HasIrreducibleDevissageIn X := by
  intro F hF hirr
  have hFc : F.IsCoherent := hF
  have hFq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact hasDevissageWith_of_killed
    ⟨SheafOfModules.supp F, DevissageNoetherian.forall_isClosed_supp X F hF⟩ _
    isIdealPushforwardIn_or_supp_ssubset_of_iso
    (h ⟨SheafOfModules.supp F, DevissageNoetherian.forall_isClosed_supp X F hF⟩ hirr) F subset_rfl

/-- **[Stacks, Tag 01YG] on step 4 of the proof of [Stacks, Tag 01YF] alone.** A property of
modules on a Noetherian scheme that holds on the zero module, is stable under extensions of
coherent modules, and holds on the direct image of every quasi-coherent ideal sheaf on every
integral closed subscheme, holds on every coherent module.

This is the statement of Tag 01YG verbatim with the single added hypothesis
`HasKilledIdealDevissage X`. -/
theorem property_of_hasKilledIdealDevissage (X : Scheme.{u}) [IsNoetherian X]
    (h : HasKilledIdealDevissage X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  IdealPowerSmul.property_of_irreducibleDevissage
    (hasIrreducibleDevissage_of_hasKilledIdealDevissage h) P hzero hext hideal

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
