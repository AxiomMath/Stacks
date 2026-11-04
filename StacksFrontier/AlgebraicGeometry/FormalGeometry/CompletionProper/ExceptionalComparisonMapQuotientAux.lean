module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# A uniform power of an ideal sheaf for the levels of a completed morphism

Let `Y` be a locally Noetherian scheme, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals and
let `c : 𝒢 ⟶ ℋ` be a morphism of coherent `𝒪_Y`-modules whose kernel and cokernel are both
annihilated by `𝒦 ᵗ`. Completing along `𝒥` produces the morphism of inverse systems
`c^ : 𝒢^ ⟶ ℋ^` of Stacks 0880, whose level `n` is the induced map

`α_n : 𝒢 / 𝒥 ⁿ⁺¹𝒢 ⟶ ℋ / 𝒥 ⁿ⁺¹ℋ`.

This file proves that **one** power of `𝒦` — namely `𝒦 ²ᵗ`, independent of `n` — annihilates the
kernel and the cokernel of every `α_n` at once, which is the hypothesis
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` of Tag 0889.

The argument is elementwise on an affine open `U`, where `A = Γ(Y, U)` acts on
`Gᵤ = Γ(𝒢, U)` and `Hᵤ = Γ(ℋ, U)`. For the cokernel, an `r ∈ 𝒦(U)ᵗ` carries every section of
`ℋ` into the image of `c`, hence every section of `ℋ_n` into the image of `α_n`: already `𝒦 ᵗ`
suffices. For the kernel, a section of `Ker(α_n)` lifts to `x ∈ Gᵤ` with
`c(x) = Σ aᵢ yᵢ` and `aᵢ ∈ 𝒥(U)ⁿ⁺¹`; writing `r yᵢ = c(gᵢ)` exhibits `r x - Σ aᵢ gᵢ` as a section
of `Ker(c)`, which a second `s ∈ 𝒦(U)ᵗ` kills, so `(s r) x = Σ aᵢ (s gᵢ)` lies in
`𝒥(U)ⁿ⁺¹ Gᵤ` and dies in `𝒢_n`. Products `s r` generate `𝒦(U)²ᵗ`, whence the exponent `2t`.

## Main results

* `Stacks.Coherent.smul_eq_zero_of_app_eq_zero_affine` — a power of `𝒦` annihilating `Ker(f)`
  kills every section of the source over an affine open which `f` sends to zero.
* `Stacks.Coherent.smul_mem_range_of_cokernel_eq_bot_affine` — a power of `𝒦` annihilating
  `Coker(f)` carries every section of the target over an affine open into the image of `f`.
* `Stacks.Coherent.idealPowerMultiple_cokernel_completionFunctor_map_eq_bot` — `𝒦 ᵗ` annihilates
  the cokernel of every level of `c^`.
* `Stacks.Coherent.idealPowerMultiple_kernel_completionFunctor_map_eq_bot` — `𝒦 ²ᵗ` annihilates
  the kernel of every level of `c^`.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_completionFunctor_map` — **the uniform
  exponent**: the levelwise kernels and cokernels of `c^` are annihilated by the single power
  `𝒦 ²ᵗ`.

## Implementation notes

Three surjectivity statements about sections drive the proof, and all three are already in the
library rather than reproved here. Sections of a categorical kernel are the sections killed by
the morphism, in both directions:
`Stacks.Algebraization.exists_kernel_section` and
`Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι`, neither needing quasi-coherence,
since evaluation at an open preserves finite limits. Over an *affine* open and for
quasi-coherent modules evaluation is exact, which is
`Stacks.Algebraization.affine_sections_cokernel_exact` and, for an epimorphism,
`AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen`. The projection
`𝒢 ⟶ 𝒢 / 𝒥 ⁿ⁺¹𝒢` is handled by the two statements specific to it,
`Stacks.Algebraization.completionProjection_app_surjective` and
`Stacks.Algebraization.completionProjection_app_ker`, the second identifying its kernel on
affine sections with `𝒥(U)ⁿ⁺¹ Gᵤ`; this is what turns the sheaf-level quotient into the honest
module quotient the elementwise argument manipulates.

`AlgebraicGeometry.Scheme.Modules` is a semireducible definition, so the module structure on the
sections of an object presented as a bare `SheafOfModules Y.ringCatSheaf` — which is how the
underlying module of an object of `AlgebraicGeometry.SheafOfModules.CoherentModules` is
presented — is not found by instance search. The bridging `local instance`s of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent` and of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections` are reactivated
here rather than restated, so that the instances in the statements imported from the latter file
are the ones the goals here carry.

The passage from the two exponents `t` to the single exponent `2t` is
`Submodule.smul_induction_on` on the membership `c(x) ∈ 𝒥(U)ⁿ⁺¹ Hᵤ` together with
`Ideal.mul_le` against the kernel of `LinearMap.toSpanSingleton`, which is the ideal of scalars
killing a fixed section.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ Stacks.Algebraization.monoSubmoduleι
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

namespace Stacks.Coherent

variable {Y : Scheme.{u}}

/-! ### Annihilation of sections through a kernel and a cokernel -/

/-- **A power of `𝒦` annihilating `Ker(f)` kills the sections it sees as killed by `f`.** If
`𝒦 ᵗ Ker(f) = 0` and `r ∈ 𝒦(U)ᵗ` for an affine open `U`, then `r` annihilates every section of
the source over `U` which `f` sends to zero.

Such a section is the image of a section of the categorical kernel, by left exactness of
evaluation at an open, and `r` kills that one. -/
public theorem smul_eq_zero_of_app_eq_zero_affine {K : Y.IdealSheafData} {t : ℕ}
    {M N : Y.Modules} (f : M ⟶ N)
    (hker : idealPowerMultiple K t (kernel (C := Y.Modules) f) = ⊥)
    (U : Y.affineOpens) {r : Γ(Y, U)} (hr : r ∈ K.ideal U ^ t) {x : Γ(M, U.1)}
    (hx : f.app U.1 x = 0) : r • x = 0 := by
  obtain ⟨y, hy⟩ := Stacks.Algebraization.exists_kernel_section f U.1 x hx
  calc
    r • x = r • (kernel.ι (C := Y.Modules) f).app U.1 y := by rw [hy]
    _ = (kernel.ι (C := Y.Modules) f).app U.1 (r • y) :=
      (Scheme.Modules.Hom.app_smul _ _ _).symm
    _ = 0 := by
      rw [affine_sections_annihilated_of_idealPowerMultiple_eq_bot hker U hr y, map_zero]

/-- **A power of `𝒦` annihilating `Coker(f)` pushes sections into the image of `f`.** If
`𝒦 ᵗ Coker(f) = 0` and `r ∈ 𝒦(U)ᵗ` for an affine open `U`, then `r y` is the image of a section
of the source over `U`, for every section `y` of the target.

The class of `r y` in the cokernel vanishes, and over an affine open evaluation is exact on
quasi-coherent modules. -/
public theorem smul_mem_range_of_cokernel_eq_bot_affine {K : Y.IdealSheafData} {t : ℕ}
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hcok : idealPowerMultiple K t (cokernel (C := Y.Modules) f) = ⊥)
    (U : Y.affineOpens) {r : Γ(Y, U)} (hr : r ∈ K.ideal U ^ t) (y : Γ(N, U.1)) :
    ∃ x : Γ(M, U.1), f.app U.1 x = r • y := by
  have hzero : (cokernel.π (C := Y.Modules) f).app U.1 (r • y) = 0 := by
    rw [Scheme.Modules.Hom.app_smul]
    exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hcok U hr _
  exact (Stacks.Algebraization.affine_sections_cokernel_exact f U (r • y)).mp hzero

/-- A coherent module is quasi-coherent. -/
private theorem isQuasicoherent_obj_of_coherentModules
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    G.obj.IsQuasicoherent := by
  have : G.obj.IsCoherent := G.property
  exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G.obj).1

/-! ### The levels of a completed morphism -/

section Levels

variable [IsLocallyNoetherian Y] (J K : Y.IdealSheafData)
  {G H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (c : G ⟶ H)

/-- The projection to level `n` intertwines `c` with the level `n` of `c^` on affine sections. -/
private theorem app_completionProjection_app_hom (n : ℕ) (U : Y.affineOpens)
    (x : Γ(G.obj, U.1)) :
    Scheme.Modules.Hom.app (completionProjection Y J H n) U.1 (Scheme.Modules.Hom.app c.hom U.1 x) =
      Scheme.Modules.Hom.app (((completionFunctor Y J).map c).hom.app (op n)) U.1
        (Scheme.Modules.Hom.app (completionProjection Y J G n) U.1 x) :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ U.1 x)
    (completionFunctor_map_quotient Y J c n).symm

/-- **`𝒦 ᵗ` annihilates the cokernel of every level of `c^`.** If `𝒦 ᵗ` annihilates `Coker(c)`
then it annihilates `Coker(α_n)` for every `n`, with no increase of the exponent.

A section of `Coker(α_n)` over an affine open lifts to `ℋ_n` and then to `ℋ`, where `𝒦(U)ᵗ`
pushes it into the image of `c`; the defining relation
`Stacks.Algebraization.completionFunctor_map_quotient` carries that image into the image of
`α_n`. -/
public theorem idealPowerMultiple_cokernel_completionFunctor_map_eq_bot {t : ℕ}
    (hcok : idealPowerMultiple K t (cokernel (C := Y.Modules) c.hom) = ⊥) (n : ℕ) :
    idealPowerMultiple K t
      (cokernel (((completionFunctor Y J).map c).hom.app (op n))) = ⊥ := by
  have hGc : G.obj.IsCoherent := G.property
  have hHc : H.obj.IsCoherent := H.property
  have hGq := isQuasicoherent_obj_of_coherentModules G
  have hHq := isQuasicoherent_obj_of_coherentModules H
  set β := ((completionFunctor Y J).map c).hom.app (op n) with hβ
  have hGn : (((completionFunctor Y J).obj G).obj.obj (op n)).IsCoherent :=
    ((completionFunctor Y J).obj G).property.1 n
  have hHn : (((completionFunctor Y J).obj H).obj.obj (op n)).IsCoherent :=
    ((completionFunctor Y J).obj H).property.1 n
  have hGnq : (((completionFunctor Y J).obj G).obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hHnq : (((completionFunctor Y J).obj H).obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hCc : (cokernel β).IsCoherent := AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel β
  have hCq : (cokernel β).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hepi : Epi (C := Y.Modules) (cokernel.π β) := coequalizer.π_epi
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U r hr z => ?_
  obtain ⟨w, hw⟩ :=
    AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen (cokernel.π β) U.2 z
  obtain ⟨y, hy⟩ : ∃ y : Γ(H.obj, U.1),
      Scheme.Modules.Hom.app (completionProjection Y J H n) U.1 y = w :=
    completionProjection_app_surjective Y J H n U w
  obtain ⟨x, hx⟩ := smul_mem_range_of_cokernel_eq_bot_affine c.hom hcok U hr y
  have hrw : r • w = Scheme.Modules.Hom.app (completionProjection Y J H n) U.1
      (Scheme.Modules.Hom.app c.hom U.1 x) := by
    rw [hx, ← hy]
    exact (Scheme.Modules.Hom.app_smul _ _ _).symm
  calc
    r • z = r • Scheme.Modules.Hom.app (cokernel.π β) U.1 w := by rw [hw]
    _ = Scheme.Modules.Hom.app (cokernel.π β) U.1 (r • w) :=
        (Scheme.Modules.Hom.app_smul _ _ _).symm
    _ = Scheme.Modules.Hom.app (cokernel.π β) U.1
          (Scheme.Modules.Hom.app β U.1
            (Scheme.Modules.Hom.app (completionProjection Y J G n) U.1 x)) := by
        rw [hrw, app_completionProjection_app_hom J c]
    _ = 0 := congrArg (fun φ => Scheme.Modules.Hom.app φ U.1
          (Scheme.Modules.Hom.app (completionProjection Y J G n) U.1 x))
          (cokernel.condition β)

/-- **`𝒦 ²ᵗ` annihilates the kernel of every level of `c^`.** If one power `𝒦 ᵗ` annihilates both
`Ker(c)` and `Coker(c)` then its square annihilates `Ker(α_n)`, for every `n`.

Over an affine open a section of `Ker(α_n)` lifts to a section `x` of `𝒢` with
`c(x) ∈ 𝒥(U)ⁿ⁺¹ Hᵤ`, say `c(x) = Σ aᵢ yᵢ`. Each `r yᵢ` with `r ∈ 𝒦(U)ᵗ` is `c(gᵢ)`, so
`r x - Σ aᵢ gᵢ` is killed by `c` and therefore by a second `s ∈ 𝒦(U)ᵗ`; hence
`(s r) x = Σ aᵢ (s gᵢ)` lies in `𝒥(U)ⁿ⁺¹ Gᵤ`, which is the kernel of the projection onto `𝒢_n`.
Such products generate `𝒦(U)²ᵗ`. -/
public theorem idealPowerMultiple_kernel_completionFunctor_map_eq_bot {t : ℕ}
    (hker : idealPowerMultiple K t (kernel (C := Y.Modules) c.hom) = ⊥)
    (hcok : idealPowerMultiple K t (cokernel (C := Y.Modules) c.hom) = ⊥) (n : ℕ) :
    idealPowerMultiple K (2 * t)
      (kernel (((completionFunctor Y J).map c).hom.app (op n))) = ⊥ := by
  have hGc : G.obj.IsCoherent := G.property
  have hHc : H.obj.IsCoherent := H.property
  have hGq := isQuasicoherent_obj_of_coherentModules G
  have hHq := isQuasicoherent_obj_of_coherentModules H
  set β := ((completionFunctor Y J).map c).hom.app (op n) with hβ
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U ρ hρ z => ?_
  have hprod : ∀ s ∈ K.ideal U ^ t, ∀ r ∈ K.ideal U ^ t, (s * r) • z = 0 := by
    intro s hs r hr
    obtain ⟨x, hx⟩ : ∃ x : Γ(G.obj, U.1),
        Scheme.Modules.Hom.app (completionProjection Y J G n) U.1 x =
          Scheme.Modules.Hom.app (kernel.ι β) U.1 z :=
      completionProjection_app_surjective Y J G n U _
    have hβz : Scheme.Modules.Hom.app β U.1
        (Scheme.Modules.Hom.app (kernel.ι β) U.1 z) = 0 :=
      congrArg (fun φ => Scheme.Modules.Hom.app φ U.1 z) (kernel.condition β)
    have hqc : Scheme.Modules.Hom.app (completionProjection Y J H n) U.1
        (Scheme.Modules.Hom.app c.hom U.1 x) = 0 := by
      rw [app_completionProjection_app_hom J c, hx]
      exact hβz
    have hmem := (completionProjection_app_eq_zero_iff Y J H n U _).1 hqc
    rw [idealPowerMultiple_toSubmodule_obj_affine J (n + 1) H.obj U] at hmem
    have hlift : ∀ v : Γ(H.obj, U.1),
        v ∈ J.ideal U ^ (n + 1) • (⊤ : Submodule Γ(Y, U) Γ(H.obj, U.1)) →
        ∃ w : Γ(G.obj, U.1),
          w ∈ J.ideal U ^ (n + 1) • (⊤ : Submodule Γ(Y, U) Γ(G.obj, U.1)) ∧
            Scheme.Modules.Hom.app c.hom U.1 w = r • v := by
      intro v hv
      refine Submodule.smul_induction_on hv ?_ ?_
      · intro a ha v' _
        obtain ⟨x', hx'⟩ := smul_mem_range_of_cokernel_eq_bot_affine c.hom hcok U hr v'
        refine ⟨a • x', Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
        erw [Scheme.Modules.Hom.app_smul, hx', ← mul_smul, ← mul_smul, mul_comm a r]
      · rintro v₁ v₂ ⟨w₁, hw₁, e₁⟩ ⟨w₂, hw₂, e₂⟩
        exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂, smul_add]⟩
    obtain ⟨w, hwmem, hwc⟩ := hlift _ hmem
    have hsub : Scheme.Modules.Hom.app c.hom U.1 (r • x - w) = 0 := by
      erw [map_sub, Scheme.Modules.Hom.app_smul, hwc, sub_self]
    have hs0 : s • (r • x - w) = 0 :=
      smul_eq_zero_of_app_eq_zero_affine c.hom hker U hs hsub
    rw [smul_sub, sub_eq_zero] at hs0
    have hGker : Scheme.Modules.Hom.app (completionProjection Y J G n) U.1
        ((s * r) • x) = 0 := by
      refine (completionProjection_app_eq_zero_iff Y J G n U _).2 ?_
      rw [idealPowerMultiple_toSubmodule_obj_affine J (n + 1) G.obj U, mul_smul, hs0]
      exact Submodule.smul_mem _ s hwmem
    have hgz : Scheme.Modules.Hom.app (kernel.ι β) U.1 ((s * r) • z) = 0 := by
      erw [Scheme.Modules.Hom.app_smul, ← hx, ← Scheme.Modules.Hom.app_smul]
      exact hGker
    exact Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι β U.1
      (hgz.trans (map_zero _).symm)
  have hle : K.ideal U ^ (2 * t) ≤
      LinearMap.ker (LinearMap.toSpanSingleton Γ(Y, U) Γ(kernel β, U.1) z) := by
    rw [two_mul, pow_add]
    exact Ideal.mul_le.2 fun s hs r hr => hprod s hs r hr
  exact hle hρ

end Levels

/-! ### The uniform exponent -/

/-- **One power of `𝒦` annihilates the levelwise kernels and cokernels of a completed
morphism.** Let `Y` be a locally Noetherian scheme, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of
ideals and let `c : 𝒢 ⟶ ℋ` be a morphism of coherent `𝒪_Y`-modules whose kernel and cokernel are
annihilated by `𝒦 ᵗ` for a single positive `t`. Then `𝒦 ²ᵗ` annihilates the kernel and the
cokernel of *every* level of the completion `c^ : 𝒢^ ⟶ ℋ^` along `𝒥`.

The point is that the exponent does not grow with the level: this is exactly the hypothesis
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` that Tag 0889 consumes, and the
cokernel half even holds with the exponent `t`. -/
public theorem isKernelCokernelAnnihilatedByPower_completionFunctor_map
    [IsLocallyNoetherian Y] (J K : Y.IdealSheafData)
    {G H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (c : G ⟶ H)
    {t : ℕ} (ht : 0 < t)
    (hker : Stacks.Algebraization.idealPowerMultiple K t
      (kernel (C := Y.Modules) c.hom) = ⊥)
    (hcok : Stacks.Algebraization.idealPowerMultiple K t
      (cokernel (C := Y.Modules) c.hom) = ⊥) :
    Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower K
      ((Stacks.Algebraization.completionFunctor Y J).map c).hom :=
  ⟨2 * t, by omega, fun n =>
    ⟨idealPowerMultiple_kernel_completionFunctor_map_eq_bot J K c hker hcok n,
      idealPowerMultiple_eq_bot_of_le
        (idealPowerMultiple_cokernel_completionFunctor_map_eq_bot J K c hcok n) (by omega)⟩⟩

end Stacks.Coherent

end
