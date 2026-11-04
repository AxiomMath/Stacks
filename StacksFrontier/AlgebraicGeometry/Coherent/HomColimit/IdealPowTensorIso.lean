module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowTensorSmul
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerBridge
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubmoduleFactorAffine
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an isomorphism for large `m`

Let `X` be a Noetherian scheme, let `I` be a quasi-coherent sheaf of ideals on `X` and let `G` be
a coherent `𝒪_X`-module.  Multiplication of sections is an epimorphism
`Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` whose kernel `𝒦` is annihilated by `Iⁿ`.  Restricting it to the subsheaf
`Iᵐ(Iⁿ ⊗_{𝒪_X} G)` gives a morphism

`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G`

which is an epimorphism for every `m` and, for all large `m`, also a monomorphism: by Artin-Rees
the intersection of `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` with `𝒦` is contained in `Iⁿ 𝒦 = 0` once `m` exceeds the
Artin-Rees constant by `n`.  So the morphism is an isomorphism for all large `m`.

## Main definitions

* `tensorMultipleToModule`: the composite `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ Iⁿ ⊗_{𝒪_X} G ⟶ G`, multiplication
  of sections restricted to the subsheaf.
* `idealPowSmulTensorToSmul`: **the morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G`**, the factorization
  of that composite through the subsheaf `I^{n+m} G` of `G`.
* `tensorKer`: the kernel of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`, as a subsheaf of `Iⁿ ⊗_{𝒪_X} G`.

## Main results

* `isQuasicoherent_tensorModules`: a tensor product of quasi-coherent `𝒪_X`-modules is
  quasi-coherent, in the spelling of `Stacks.AlgebraicGeometry.IdealProduct.tensorModules`.
* `isCoherent_tensorModules_idealPow`: **`Iⁿ ⊗_{𝒪_X} G` is coherent** for `G` coherent on a
  locally Noetherian scheme.
* `exists_preimage_idealPowSmulTensorToSmul`: every section of `I^{n+m} G` over an affine open is
  the image of a section of `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` over that same open.
* `epi_idealPowSmulTensorToSmul`: **`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an epimorphism**, for
  every `m`.
* `eq_zero_of_mem_idealPow_smul_tensorKer`: `Iⁿ 𝒦 = 0` read on an affine open, where `𝒦` is the
  kernel of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`.
* `exists_mono_idealPowSmulTensorToSmul`: **`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is a monomorphism**
  for all large `m`.
* `exists_isIso_idealPowSmulTensorToSmul`: **`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an isomorphism**
  for all large `m`.  This is the step of the proof of the first display of [Stacks, Tag 01YB]
  that replaces the tensor product by the product of subsheaves.

## Implementation notes

**Coherence of `Iⁿ ⊗_{𝒪_X} G` is Tag 01CE (6).**  No invertibility of either factor is needed:
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` tensors two coherent sheaves of
modules, and `AlgebraicGeometry.isCoherent_idealPow` makes `Iⁿ` coherent.  Both hypotheses have
to be passed as terms rather than found by instance search, because the sheaf of rings is spelled
`structureSheafRing X.toRingedSpace` there and
`X.ringCatSheaf` here; the two are
equal by `rfl` but not at the transparency of instance resolution.

**Sections of the tensor product carry a module structure only at one spelling.**  The instance
`Module Γ(X, U) Γ(M, U)` of `AlgebraicGeometry.Scheme.Modules` is keyed on
`(Scheme.Modules.presheaf M).obj (op U)`, so a section whose type has been elaborated as
`M.val.obj (op U)` instead — which is what `set` produces for a value built by
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, and what the carrier of a
`PresheafOfModules.Submodule.obj`
is — is not a module and cannot be multiplied by a scalar.  Every section of
`Iⁿ ⊗_{𝒪_X} G` below is therefore introduced by `obtain` at the spelling
`Γ(tensorModules (idealPow I n) G, V)`, and every submodule of such sections that is produced by
`toSubmodule.obj` is pinned with `show _ from _` before a scalar multiple or an infimum is formed
from it, exactly as in `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq`.

**Epimorphy and monomorphy are proved in `SheafOfModules` and transported.**
`AlgebraicGeometry.Scheme.Modules` carries its own `Category` instance, so `Epi` and `Mono` there
are not the propositions the general criteria prove; each is obtained by applying the criterion
with its category argument supplied positionally and then re-deriving the cancellation property.
Monomorphy goes through injectivity on sections over every open, which follows from injectivity
over the affine opens because a section vanishing on an affine neighbourhood of each point
vanishes.

**The quantifier shape.**  Epimorphy holds for every `m`; monomorphy only for `m` beyond the
Artin-Rees constant `c` of `exists_ideal_pow_smul_inf_eq_ideal` shifted by `n`.  The statements
below therefore produce a single constant and assert the conclusion for every `m` above it, which
is what the colimit argument of Tag 01YB needs: it has to choose one `m` after `n` is given.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealProduct

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Quasi-coherence and coherence of `Iⁿ ⊗_{𝒪_X} G` -/

/-- **A tensor product of quasi-coherent `𝒪_X`-modules is quasi-coherent**, in the spelling of
the tensor product that takes its arguments in `X.Modules`. -/
public instance isQuasicoherent_tensorModules (A B : X.Modules) [A.IsQuasicoherent]
    [B.IsQuasicoherent] : (tensorModules A B).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace A B ‹_› ‹_›

/-- **`Iⁿ ⊗_{𝒪_X} G` is coherent** for a coherent `G` on a locally Noetherian scheme: both
factors are coherent, so [Stacks, Tag 01CE] (6) applies. -/
public theorem isCoherent_tensorModules_idealPow [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (n : ℕ) (G : X.Modules) (hG : G.IsCoherent) :
    (tensorModules (idealPow I n) G).IsCoherent :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace (idealPow I n) G
    (isCoherent_idealPow I n) hG

/-! ### The morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` -/

/-- Multiplication of sections restricted to `Iᵐ(Iⁿ ⊗_{𝒪_X} G)`, as a morphism
`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ G`. -/
public noncomputable abbrev tensorMultipleToModule (I : X.IdealSheafData) (n m : ℕ)
    (G : X.Modules) : idealPowSmul I m (tensorModules (idealPow I n) G) ⟶ G :=
  submoduleι (idealPowerMultiple I m (tensorModules (idealPow I n) G)) ≫
    idealPowTensorToModule I n G

/-- **Multiplication of sections on `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` takes values in `I^{n+m} G`.**  Over an
affine open a section of `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` is a finite sum `∑ aⱼ tⱼ` with `aⱼ ∈ I(V)ᵐ`, and the
product of a section of `Iⁿ ⊗_{𝒪_X} G` lies in `Iⁿ G`, so each summand lies in
`I(V)ᵐ I(V)ⁿ Γ(G, V)`. -/
public theorem mem_tensorMultipleToModule (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] (V : X.affineOpens)
    (x : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), V.1)) :
    (tensorMultipleToModule I n m G).app V.1 x ∈
      (idealPowerMultiple I (n + m) G).toSubmodule.obj (op V.1) := by
  have hx : (x.1 : Γ(tensorModules (idealPow I n) G, V.1)) ∈
      I.ideal V ^ m • (⊤ : Submodule Γ(X, V.1) Γ(tensorModules (idealPow I n) G, V.1)) :=
    (idealPowerMultiple_obj_affineOpen I m (tensorModules (idealPow I n) G) V).le x.2
  obtain ⟨k, a, t, ha, hsum⟩ := Submodule.exists_sum_smul_of_mem_smul
    (M := Γ(tensorModules (idealPow I n) G, V.1)) hx
  have hmem : ∀ j : Fin k, (idealPowTensorToModule I n G).app V.1 (t j) ∈
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(G, V.1)) := fun j ↦
    (idealPowerMultiple_obj_affineOpen I n G V).le
      ((val_idealPowTensorToSmul_app I n G V.1 (t j)) ▸
        ((idealPowTensorToSmul I n G).app V.1 (t j)).2)
  rw [idealPowerMultiple_obj_affineOpen I (n + m) G V]
  have hgoal : (tensorMultipleToModule I n m G).app V.1 x
      = ∑ j, a j • (idealPowTensorToModule I n G).app V.1 (t j) := by
    show (idealPowTensorToModule I n G).app V.1 (x.1) = _
    rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Scheme.Modules.Hom.app_smul _ _ _
  rw [hgoal]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  have hterm : a j • (idealPowTensorToModule I n G).app V.1 (t j) ∈
      I.ideal V ^ m • (I.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(G, V.1))) :=
    Submodule.smul_mem_smul (ha j) (hmem j)
  rwa [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_add, Nat.add_comm m n] at hterm

/-- **The morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G`**, the factorization of multiplication of
sections through the subsheaf `I^{n+m} G` of `G`. -/
public noncomputable def idealPowSmulTensorToSmul (I : X.IdealSheafData) (n m : ℕ)
    (G : X.Modules) [G.IsQuasicoherent] :
    idealPowSmul I m (tensorModules (idealPow I n) G) ⟶ idealPowSmul I (n + m) G :=
  factorThruOfForallAffineOpens (idealPowerMultiple I (n + m) G)
    (tensorMultipleToModule I n m G) (mem_tensorMultipleToModule I n m G)

/-- The morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` does not change the value of a section: as a
section of `G` it is the product of the factors. -/
public theorem val_idealPowSmulTensorToSmul_app (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] (V : X.Opens)
    (z : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), V)) :
    (((idealPowSmulTensorToSmul I n m G).app V z).1 : Γ(G, V)) =
      (tensorMultipleToModule I n m G).app V z := rfl

/-! ### The morphism is an epimorphism -/

/-- Every point of an open `W` has an affine open neighbourhood contained in `W`. -/
private theorem exists_affineOpen_mem_le (W : X.Opens) {p : X} (hp : p ∈ W) :
    ∃ V : X.affineOpens, p ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (W : Set X) from hp) W.isOpen
  exact ⟨⟨V, hVaff⟩, hpV, hVW⟩

/-- **A multiple `(b c) g` with `b ∈ I(V)ⁿ` and `c ∈ I(V)ᵐ` is a value of multiplication of
sections on `Iᵐ(Iⁿ ⊗_{𝒪_X} G)`**, over an affine open: the section `c (b ⊗ g)` of the tensor
product lies in `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` and multiplies out to `(b c) g`. -/
public theorem exists_preimage_mul_smul (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] (V : X.affineOpens) {b c : Γ(X, V.1)} (hb : b ∈ I.ideal V ^ n)
    (hc : c ∈ I.ideal V ^ m) (y : Γ(G, V.1)) :
    ∃ z : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), V.1),
      (tensorMultipleToModule I n m G).app V.1 z = (b * c) • y := by
  have hb' : b ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1) :=
    (obj_idealPow_affineOpen I n V).ge hb
  obtain ⟨pt, hpt⟩ : ∃ pt : Γ(tensorModules (idealPow I n) G, V.1),
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace (idealPow I
      n) G (op V.1)
        ((⟨b, hb'⟩ : Γ(idealPow I n, V.1)) ⊗ₜ[X.presheaf.obj (op V.1)] y) = pt := ⟨_, rfl⟩
  have hval : (idealPowTensorToModule I n G).app V.1 pt = b • y :=
    (congrArg (ConcreteCategory.hom ((idealPowTensorToModule I n G).app V.1)) hpt).symm.trans
      (smulToModule_app_toTensorSheafSection (idealPowInclusion I n) G V.1 ⟨b, hb'⟩ y b rfl)
  have hmem : c • pt ∈ I.ideal V ^ m •
      (⊤ : Submodule Γ(X, V.1) Γ(tensorModules (idealPow I n) G, V.1)) :=
    Submodule.smul_mem_smul hc Submodule.mem_top
  refine ⟨⟨_, (idealPowerMultiple_obj_affineOpen I m
    (tensorModules (idealPow I n) G) V).ge hmem⟩, ?_⟩
  refine Eq.trans (Scheme.Modules.Hom.app_smul (idealPowTensorToModule I n G) c pt) ?_
  refine Eq.trans (congrArg (fun w : Γ(G, V.1) ↦ c • w) hval) ?_
  exact (smul_smul c b y).trans (congrArg (fun r : Γ(X, V.1) ↦ r • y) (mul_comm c b))

/-- **Every section of `I^{n+m} G` over an affine open is the image of a section of
`Iᵐ(Iⁿ ⊗_{𝒪_X} G)` over the same open.**  The sections of `I^{n+m} G` over an affine open `V`
are `I(V)^{n+m} Γ(G, V)`, and `I(V)^{n+m}` is `I(V)ⁿ I(V)ᵐ`, so each generator is covered by
`exists_preimage_mul_smul`. -/
public theorem exists_preimage_idealPowSmulTensorToSmul (I : X.IdealSheafData) (n m : ℕ)
    (G : X.Modules) [G.IsQuasicoherent] (V : X.affineOpens)
    (y : Γ(idealPowSmul I (n + m) G, V.1)) :
    ∃ z, (idealPowSmulTensorToSmul I n m G).app V.1 z = y := by
  have hle : I.ideal V ^ (n + m) • (⊤ : Submodule Γ(X, V.1) Γ(G, V.1)) ≤
      LinearMap.range (QcohLimits.appₗ (tensorMultipleToModule I n m G) V.1) := by
    refine Submodule.smul_le.mpr fun r hr y' _ ↦ ?_
    refine Submodule.mul_induction_on
      (show r ∈ I.ideal V ^ n * I.ideal V ^ m from pow_add (I.ideal V) n m ▸ hr)
      (fun b hb c hc ↦ exists_preimage_mul_smul I n m G V hb hc y')
      fun u v hu hv ↦ ?_
    rw [add_smul]
    exact Submodule.add_mem _ hu hv
  obtain ⟨z, hz⟩ := hle ((idealPowerMultiple_obj_affineOpen I (n + m) G V).le y.2)
  exact ⟨z, Subtype.ext ((val_idealPowSmulTensorToSmul_app I n m G V.1 z).trans hz)⟩

/-- **The morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an epimorphism**, for every `m` and every
quasi-coherent `G`. -/
public theorem epi_idealPowSmulTensorToSmul (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] : Epi (idealPowSmulTensorToSmul I n m G) := by
  have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _
      (idealPowSmulTensorToSmul I n m G) := by
    refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ ?_
    obtain ⟨V, hpV, hVW⟩ := exists_affineOpen_mem_le W hp
    obtain ⟨z, hz⟩ := exists_preimage_idealPowSmulTensorToSmul I n m G V
      ((idealPowSmul I (n + m) G).val.map (homOfLE hVW).op t)
    exact ⟨V, hVW, hpV, z, hz⟩
  exact ⟨fun g₁ g₂ h ↦ hepi.left_cancellation g₁ g₂ h⟩

/-! ### The kernel of multiplication of sections -/

/-- The kernel `𝒦` of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`, as a subsheaf of `Iⁿ ⊗_{𝒪_X} G`. -/
public noncomputable abbrev tensorKer (I : X.IdealSheafData) (n : ℕ) (G : X.Modules) :
    (tensorModules (idealPow I n) G).Submodule :=
  SheafOfModules.Submodule.ker (idealPowTensorToSmul I n G)

/-- **`Iⁿ 𝒦 = 0` read on an affine open**: a section of `Iⁿ ⊗_{𝒪_X} G` lying in
`I(V)ⁿ 𝒦(V)` vanishes, each generator `a k` of that submodule doing so by
`smul_eq_zero_of_idealPowTensorToSmul_eq_zero`. -/
public theorem eq_zero_of_mem_idealPow_smul_tensorKer (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) (V : X.affineOpens) {x : Γ(tensorModules (idealPow I n) G, V.1)}
    (hx : x ∈ I.ideal V ^ n •
      (show Submodule Γ(X, V.1) Γ(tensorModules (idealPow I n) G, V.1) from
        (tensorKer I n G).toSubmodule.obj (op V.1))) : x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha k hk ↦ ?_) fun u v hu hv ↦ ?_
  · exact smul_eq_zero_of_idealPowTensorToSmul_eq_zero I n G
      ((obj_idealPow_affineOpen I n V).ge ha) hk
  · rw [hu, hv, add_zero]

/-- A section of `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` killed by `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` lies in the
kernel `𝒦` of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`: the two morphisms have the same value on it as sections
of `G`. -/
public theorem mem_tensorKer_of_app_eq_zero (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] (V : X.Opens)
    (z : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), V))
    (hz : (idealPowSmulTensorToSmul I n m G).app V z = 0) :
    (z.1 : Γ(tensorModules (idealPow I n) G, V)) ∈ (tensorKer I n G).toSubmodule.obj (op V) := by
  have h1 : ((idealPowSmulTensorToSmul I n m G).app V z).1 = (0 : Γ(G, V)) :=
    congrArg (fun w : Γ(idealPowSmul I (n + m) G, V) ↦ (w.1 : Γ(G, V))) hz
  exact Subtype.ext ((val_idealPowTensorToSmul_app I n G V z.1).trans h1)

/-! ### The morphism is a monomorphism for large `m` -/

/-- **For all large `m` the morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is injective on sections
over the affine opens.**  A section killed by it lies in `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ∩ 𝒦`, which
Artin-Rees identifies with `I^{m-c}(Iᶜ(Iⁿ ⊗_{𝒪_X} G) ∩ 𝒦)`; for `m ≥ c + n` that is contained
in `Iⁿ 𝒦`, which is zero. -/
public theorem exists_eq_zero_of_app_eq_zero_affine [IsNoetherian X] (I : X.IdealSheafData)
    (n : ℕ) (G : X.Modules) [G.IsQuasicoherent] (hG : G.IsCoherent) :
    ∃ c : ℕ, ∀ m : ℕ, c ≤ m → ∀ (V : X.affineOpens)
      (z : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), V.1)),
      (idealPowSmulTensorToSmul I n m G).app V.1 z = 0 → z = 0 := by
  let : (tensorModules (idealPow I n) G).IsCoherent :=
    isCoherent_tensorModules_idealPow I n G hG
  obtain ⟨c, hc⟩ := exists_ideal_pow_smul_inf_eq_ideal (tensorModules (idealPow I n) G)
    (tensorKer I n G) I
  refine ⟨c + n, fun m hm V z hz ↦ ?_⟩
  have hcm : c ≤ m := by omega
  have hnm : n ≤ m - c := by omega
  have hzm : (z.1 : Γ(tensorModules (idealPow I n) G, V.1)) ∈
      I.ideal V ^ m • (⊤ : Submodule Γ(X, V.1) Γ(tensorModules (idealPow I n) G, V.1)) :=
    (idealPowerMultiple_obj_affineOpen I m (tensorModules (idealPow I n) G) V).le z.2
  exact Subtype.ext (eq_zero_of_mem_idealPow_smul_tensorKer I n G V
    (Submodule.smul_mono (Ideal.pow_le_pow_right hnm) inf_le_right
      ((hc m hcm V).ge ⟨hzm, mem_tensorKer_of_app_eq_zero I n m G V.1 z hz⟩)))

/-- **For all large `m` the morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is injective on sections
over every open.**  A section killed by it is killed on an affine neighbourhood of each point of
its domain, hence vanishes. -/
public theorem exists_eq_zero_of_app_eq_zero [IsNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) [G.IsQuasicoherent] (hG : G.IsCoherent) :
    ∃ c : ℕ, ∀ m : ℕ, c ≤ m → ∀ (W : X.Opens)
      (z : Γ(idealPowSmul I m (tensorModules (idealPow I n) G), W)),
      (idealPowSmulTensorToSmul I n m G).app W z = 0 → z = 0 := by
  obtain ⟨c, hc⟩ := exists_eq_zero_of_app_eq_zero_affine I n G hG
  refine ⟨c, fun m hm W z hz ↦ eq_zero_of_locally_zero z fun p hp ↦ ?_⟩
  obtain ⟨V, hpV, hVW⟩ := exists_affineOpen_mem_le W hp
  refine ⟨V, hVW, hpV, hc m hm V _ ?_⟩
  refine Eq.trans (app_naturality (idealPowSmulTensorToSmul I n m G) hVW z).symm ?_
  rw [hz]
  exact map_zero _

/-- **For all large `m` the morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is a monomorphism.** -/
public theorem exists_mono_idealPowSmulTensorToSmul [IsNoetherian X] (I : X.IdealSheafData)
    (n : ℕ) (G : X.Modules) [G.IsQuasicoherent] (hG : G.IsCoherent) :
    ∃ c : ℕ, ∀ m : ℕ, c ≤ m → Mono (idealPowSmulTensorToSmul I n m G) := by
  obtain ⟨c, hc⟩ := exists_eq_zero_of_app_eq_zero I n G hG
  refine ⟨c, fun m hm ↦ ?_⟩
  have hinj : ∀ ⦃U : (X.Opens)ᵒᵖ⦄, Function.Injective
      (PresheafOfModules.Hom.app (idealPowSmulTensorToSmul I n m G).val U) := by
    intro U a b hab
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = U := ⟨U.unop, rfl⟩
    refine sub_eq_zero.mp (hc m hm W (a - b) ?_)
    refine Eq.trans (map_sub (ConcreteCategory.hom
      ((idealPowSmulTensorToSmul I n m G).app W)) a b) ?_
    exact sub_eq_zero.mpr hab
  have hmono : @Mono (SheafOfModules.{u} X.ringCatSheaf) _ _ _
      (idealPowSmulTensorToSmul I n m G) :=
    Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf)
      (PresheafOfModules.mono_of_injective hinj)
  exact ⟨fun g₁ g₂ e ↦ hmono.right_cancellation g₁ g₂ e⟩

/-! ### The isomorphism -/

/-- **For all large `m` the morphism `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an isomorphism**, for a
coherent `G` on a Noetherian scheme: it is always an epimorphism, it is a monomorphism beyond the
Artin-Rees constant, and `X.Modules` is balanced.

This is the step of the proof of the first display of [Stacks, Tag 01YB] that replaces the tensor
product `Iⁿ ⊗_{𝒪_X} G` by the subsheaf `Iⁿ G` of `G`. -/
public theorem exists_isIso_idealPowSmulTensorToSmul [IsNoetherian X] (I : X.IdealSheafData)
    (n : ℕ) (G : X.Modules) [G.IsQuasicoherent] (hG : G.IsCoherent) :
    ∃ c : ℕ, ∀ m : ℕ, c ≤ m → IsIso (idealPowSmulTensorToSmul I n m G) := by
  obtain ⟨c, hc⟩ := exists_mono_idealPowSmulTensorToSmul I n G hG
  refine ⟨c, fun m hm ↦ ?_⟩
  have := hc m hm
  have := epi_idealPowSmulTensorToSmul I n m G
  exact isIso_of_mono_of_epi _

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

end
