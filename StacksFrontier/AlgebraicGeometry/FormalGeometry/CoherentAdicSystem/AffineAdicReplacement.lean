module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.RingTheory.Module.AdicSystem.ExtensionAdicReplacement

/-!
# An adic replacement of global sections on an affine scheme is a coherent adic system

Let `W` be a Noetherian affine scheme with `R = Γ(W, 𝒪_W)`, let `𝒥` be a quasi-coherent ideal
sheaf on `W` with global ideal `I = 𝒥(W)`, and let `(ℱₙ)` be an object of `Coh(W, 𝒥)`. Let
`(Pₙ)` be an inverse system of coherent `𝒪_W`-modules with a map `τ : (ℱₙ) → (Pₙ)`. Suppose that
on global sections `(Pₙ)` is pro-isomorphic to the `I`-adic tower `(M/I^{n+1}M)` of an `R`-module
`M` whose quotients `M/I^{n+1}M` are finite, through a pro-isomorphism `e₀`, and that a map
`σ₀ : (Γ(W, ℱₙ)) → (M/I^{n+1}M)` of inverse systems is compatible with `τ` and `e₀`.

Then the sheaves `(M/I^{n+1}M)^~` form an object `(𝒩ₙ)` of `Coh(W, 𝒥)` and the data lift to
sheaves: a pro-isomorphism `(Pₙ) ≅ (𝒩ₙ)` and a morphism `σ : (ℱₙ) → (𝒩ₙ)` of `Coh(W, 𝒥)`
compatible with `τ`. Moreover a power `I^c` annihilating the kernels, respectively the cokernels,
of the module maps `σ₀` annihilates the terms of the kernel, respectively the cokernel, of `σ`
in the abelian category `Coh(W, 𝒥)`.

This is the local datum consumed by the gluing of adic replacements in the proofs of
[Stacks, Tag 0EJE] and [Stacks, Tag 0EJF], where the module-level replacement is constructed
from the inverse limit of the global sections.

## Main results

* `Stacks.Coherent.exists_coherentAdicSystem_of_affineAdicReplacement` — the lift of a
  module-level adic replacement to an object of `Coh(W, 𝒥)`, with the comparison morphism and
  the transfer of kernel and cokernel annihilation.

## Proof outline

On an affine scheme the functor `M ↦ M^~` is left adjoint to global sections with invertible
unit (`Stacks.Coherent.affineTildeAdjunction`), and global sections are fully faithful on
quasi-coherent modules (`Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful`). So every map
of global sections lifts uniquely, and every equation between maps of quasi-coherent modules can
be checked on global sections. The tower `(M/I^{n+1}M)^~` is a coherent adic system because its
terms are coherent (`M/I^{n+1}M` is finite), annihilated by `𝒥^{n+1}`, and the surjection
`M/I^{n+2}M → M/I^{n+1}M` with kernel `I^{n+1}(M/I^{n+2}M)` becomes the sheaf quotient by
`𝒥^{n+1}` (`Stacks.Coherent.affineTildeQuotientIso`).

For the annihilation statements, the terms of the kernel and the cokernel in `Coh(W, 𝒥)` are
annihilated by whatever annihilates the levelwise kernels and cokernels
(`Stacks.Coherent.idealPowerMultiple_kernel_obj_eq_bot_of_termwise` and its cokernel
counterpart). A levelwise kernel injects into `ℱₙ` on global sections, where it lands in the
kernel of `σ₀`. A levelwise cokernel is a quotient of `𝒩ₙ` that is surjective on global sections
by the vanishing of higher cohomology on affines
(`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`),
so its global sections are a quotient of the cokernel of `σ₀`.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W), coherent adic systems
  on an affine scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open InverseSequence Stacks.AdicSystem Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

section Quotients

variable {R : Type u} [CommRing R] (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N]

/-- The quotient `N/I^kN` is annihilated by `I^k`. -/
private theorem pow_smul_top_quotient_eq_bot (k : ℕ) :
    I ^ k • (⊤ : Submodule R (N ⧸ (I ^ k • (⊤ : Submodule R N)))) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- The transition maps of the `I`-adic tower are surjective. -/
private theorem adicQuotientMap_surjective {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (adicQuotientMap I N h) := fun y => by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The kernel of `N/I^{n+2}N → N/I^{n+1}N` is `I^{n+1}(N/I^{n+2}N)`. -/
private theorem ker_adicQuotientMap_succ (n : ℕ) :
    LinearMap.ker (adicQuotientMap I N (Nat.le_succ n)) =
      I ^ (n + 1) • (⊤ : Submodule R (N ⧸ (I ^ (n + 1 + 1) • (⊤ : Submodule R N)))) := by
  rw [adicQuotientMap, Submodule.ker_mapQ, Submodule.comap_id,
    map_smul_top_local _ _ (Submodule.mkQ_surjective _)]

end Quotients

variable {W : Scheme.{u}} [IsAffine W]

/-- On an affine scheme a quasi-coherent ideal sheaf is the one attached to its global ideal. -/
private theorem eq_ofIdealTop_ideal (J : W.IdealSheafData) :
    J = Scheme.IdealSheafData.ofIdealTop (J.ideal ⟨⊤, isAffineOpen_top W⟩) := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  exact (Scheme.IdealSheafData.map_ideal J (U := U) (V := ⟨⊤, isAffineOpen_top W⟩)
    (show (U : W.Opens) ≤ ⊤ from le_top)).symm

/-- **The tower `(N/I^{n+1}N)^~` is a coherent adic system** for the ideal sheaf attached to `I`,
when the quotients `N/I^{n+1}N` are finite over the Noetherian ring `Γ(W, ⊤)`. -/
private theorem isCoherentAdicSystem_adicQuotientTower_comp_affineTilde
    [IsNoetherianRing Γ(W, ⊤)] (I : Ideal Γ(W, ⊤)) (N : Type u) [AddCommGroup N]
    [Module Γ(W, ⊤) N]
    (hfin : ∀ n : ℕ, Module.Finite Γ(W, ⊤) (N ⧸ (I ^ (n + 1) • (⊤ : Submodule Γ(W, ⊤) N)))) :
    IsCoherentAdicSystem (Scheme.IdealSheafData.ofIdealTop I)
      (adicQuotientTower I N ⋙ affineTilde W) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have : Module.Finite Γ(W, ⊤) ((adicQuotientTower I N).obj (op n)) := hfin n
    exact affineTilde_coherent W ((adicQuotientTower I N).obj (op n))
  · have : ((adicQuotientTower I N ⋙ affineTilde W).obj (op n)).IsQuasicoherent :=
      affineTilde_quasicoherent W ((adicQuotientTower I N).obj (op n))
    exact affine_idealPowerMultiple_eq_bot I (n + 1) _
      (affineTilde_power_annihilates W I (n + 1) _ (pow_smul_top_quotient_eq_bot I N (n + 1)))
  · obtain ⟨e, he⟩ := affineTildeQuotientIso W I (n + 1)
      ((adicQuotientTower I N).map (homOfLE (Nat.le_succ n)).op)
      (adicQuotientMap_surjective I N (Nat.le_succ n)) (ker_adicQuotientMap_succ I N n)
    exact ⟨e, he⟩

variable [IsNoetherian W]

/-- **A module-level adic replacement on an affine scheme lifts to `Coh(W, 𝒥)`.** Let `W` be a
Noetherian affine scheme, `𝒥` an ideal sheaf on `W` with global ideal `I`, `(ℱₙ)` an object of
`Coh(W, 𝒥)`, `(Pₙ)` an inverse system of coherent modules and `τ : (ℱₙ) → (Pₙ)`. Let `M` be a
`Γ(W, ⊤)`-module with `M/I^{n+1}M` finite for all `n`, let `e₀` be a pro-isomorphism from the
global sections of `(Pₙ)` to the tower `(M/I^{n+1}M)`, and let `σ₀ : (Γ(W, ℱₙ)) → (M/I^{n+1}M)`
be a map of inverse systems with `e₀.φ n ∘ Γ(τ) = σ₀ n ∘ Γ(ℱ_{α n} → ℱₙ)`.

Then there are an object `(𝒩ₙ)` of `Coh(W, 𝒥)`, a pro-isomorphism `e : (Pₙ) ≅ (𝒩ₙ)` and a
morphism `σ : (ℱₙ) → (𝒩ₙ)` of `Coh(W, 𝒥)` with `e.φ n ∘ τ = σ n ∘ (ℱ_{α n} → ℱₙ)`, such that
for every `c`, if `I^c` annihilates the kernels of the `σ₀ n` then `𝒥^c` annihilates the terms of
the kernel of `σ`, and if `I^c` maps `M/I^{n+1}M` into the image of `σ₀ n` for all `n` then `𝒥^c`
annihilates the terms of the cokernel of `σ`.

The object is `𝒩ₙ = (M/I^{n+1}M)^~`, and `e` and `σ` are the unique lifts of `e₀` and `σ₀`
composed with the unit `M/I^{n+1}M ≅ Γ(W, 𝒩ₙ)`. -/
public theorem exists_coherentAdicSystem_of_affineAdicReplacement
    (J : W.IdealSheafData) (F : CoherentAdicSystems J) (P : ℕᵒᵖ ⥤ W.Modules)
    [∀ n, (P.obj n).IsCoherent] (τ : F.obj ⟶ P)
    (M : Type u) [AddCommGroup M] [Module Γ(W, ⊤) M]
    (hfin : ∀ n : ℕ, Module.Finite Γ(W, ⊤)
      (M ⧸ (J.ideal ⟨⊤, isAffineOpen_top W⟩ ^ (n + 1) • (⊤ : Submodule Γ(W, ⊤) M))))
    (e₀ : ProIso (P ⋙ moduleGlobalSections W)
      (adicQuotientTower (J.ideal ⟨⊤, isAffineOpen_top W⟩) M))
    (σ₀ : (F.obj ⋙ moduleGlobalSections W) ⟶
      adicQuotientTower (J.ideal ⟨⊤, isAffineOpen_top W⟩) M)
    (hσ₀ : ∀ n : ℕ,
      (moduleGlobalSections W).map (τ.app (op (e₀.α n))) ≫ e₀.φ n =
        (moduleGlobalSections W).map
          (F.obj.map (homOfLE (e₀.αle n)).op) ≫ σ₀.app (op n)) :
    ∃ (N : CoherentAdicSystems J) (e : ProIso P N.obj) (σ : F ⟶ N),
      (∀ n : ℕ, τ.app (op (e.α n)) ≫ e.φ n = F.obj.map (homOfLE (e.αle n)).op ≫ σ.hom.app (op n)) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(W, ⊤)), a ∈ J.ideal ⟨⊤, isAffineOpen_top W⟩ ^ c →
          ∀ q : Γ(F.obj.obj (op n), ⊤), (σ₀.app (op n)).hom q = 0 → a • q = 0) →
        ∀ n : ℕ, idealPowerMultiple J c ((kernel σ).obj.obj (op n)) = ⊥) ∧
      (∀ c : ℕ, (∀ (n : ℕ) (a : Γ(W, ⊤)), a ∈ J.ideal ⟨⊤, isAffineOpen_top W⟩ ^ c →
          ∀ q : (adicQuotientTower (J.ideal ⟨⊤, isAffineOpen_top W⟩) M).obj (op n),
            a • q ∈ LinearMap.range (σ₀.app (op n)).hom) →
        ∀ n : ℕ, idealPowerMultiple J c ((cokernel σ).obj.obj (op n)) = ⊥) := by
  have : IsNoetherianRing Γ(W, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top W⟩
  have hJ : J = Scheme.IdealSheafData.ofIdealTop (J.ideal ⟨⊤, isAffineOpen_top W⟩) :=
    eq_ofIdealTop_ideal J
  let E := moduleGlobalSections W
  let Q := adicQuotientTower (J.ideal ⟨⊤, isAffineOpen_top W⟩) M
  let T : ℕᵒᵖ ⥤ W.Modules := Q ⋙ affineTilde W
  have hT : IsCoherentAdicSystem J T := by
    have h := isCoherentAdicSystem_adicQuotientTower_comp_affineTilde
      (J.ideal ⟨⊤, isAffineOpen_top W⟩) M hfin
    rwa [← hJ] at h
  let N : CoherentAdicSystems J := ⟨T, hT⟩
  have hTq : ∀ n, (T.obj n).IsQuasicoherent := fun n => affineTilde_quasicoherent W _
  have hPq : ∀ n, (P.obj n).IsQuasicoherent := fun n => isQuasicoherent_of_isCoherent _
  have hFc : ∀ n, (F.obj.obj n).IsCoherent := fun n => F.property.1 n.unop
  have hFq : ∀ n, (F.obj.obj n).IsQuasicoherent := fun n => isQuasicoherent_of_isCoherent _
  let v : ∀ n : ℕᵒᵖ, Q.obj n ≅ E.obj (T.obj n) := fun n => affineTildeSectionsIso W (Q.obj n)
  have hv : ∀ {n n' : ℕᵒᵖ} (g : n ⟶ n'), Q.map g ≫ (v n').hom = (v n).hom ≫ E.map (T.map g) :=
    fun g => (affineTildeAdjunction W).unit.naturality (Q.map g)
  have hv' : ∀ {n n' : ℕᵒᵖ} (g : n ⟶ n'), E.map (T.map g) ≫ (v n').inv = (v n).inv ≫ Q.map g := by
    intro n n' g
    rw [Iso.comp_inv_eq, Category.assoc, hv g, Iso.inv_hom_id_assoc]
  have hL : ∀ {A B : W.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
      (f : E.obj A ⟶ E.obj B), E.map (affineQuasicoherentHomLift f) = f :=
    fun f => affineQuasicoherentHomLift_map f
  have hext : ∀ {A B : W.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] {f g : A ⟶ B},
      E.map f = E.map g → f = g := fun h => affineQuasicoherentHom_ext h
  obtain ⟨s, hs⟩ : ∃ s : ∀ n : ℕᵒᵖ, F.obj.obj n ⟶ T.obj n,
      ∀ n, E.map (s n) = σ₀.app n ≫ (v n).hom :=
    ⟨fun n => affineQuasicoherentHomLift _, fun n => hL _⟩
  obtain ⟨φs, hφs⟩ : ∃ φs : ∀ m : ℕ, P.obj (op (e₀.α m)) ⟶ T.obj (op m),
      ∀ m, E.map (φs m) = e₀.φ m ≫ (v (op m)).hom :=
    ⟨fun m => affineQuasicoherentHomLift _, fun m => hL _⟩
  obtain ⟨ψs, hψs⟩ : ∃ ψs : ∀ m : ℕ, T.obj (op (e₀.β m)) ⟶ P.obj (op m),
      ∀ m, E.map (ψs m) = (v (op (e₀.β m))).inv ≫ e₀.ψ m :=
    ⟨fun m => affineQuasicoherentHomLift _, fun m => hL _⟩
  -- the comparison morphism
  let σT : F.obj ⟶ T :=
    { app := s
      naturality := by
        intro n n' g
        refine hext ?_
        rw [E.map_comp, E.map_comp, hs, hs, ← Category.assoc,
          show E.map (F.obj.map g) = (F.obj ⋙ E).map g from rfl,
          σ₀.naturality g, Category.assoc, hv g, Category.assoc] }
  let σ : F ⟶ N := ObjectProperty.homMk σT
  have hσE : ∀ n, E.map (σ.hom.app n) = σ₀.app n ≫ (v n).hom := hs
  -- the pro-isomorphism
  let e : ProIso P N.obj :=
    { α := e₀.α
      β := e₀.β
      αmono := e₀.αmono
      βmono := e₀.βmono
      αle := e₀.αle
      βle := e₀.βle
      φ := φs
      ψ := ψs
      φnat := by
        intro m m' h
        refine hext ?_
        rw [E.map_comp, E.map_comp, hφs, hφs, ← Category.assoc,
          show E.map (tr P (e₀.αmono h)) = tr (P ⋙ E) (e₀.αmono h) from rfl,
          e₀.φnat h, Category.assoc, Category.assoc]
        exact congrArg (e₀.φ m' ≫ ·) (hv (homOfLE h).op)
      ψnat := by
        intro m m' h
        refine hext ?_
        rw [E.map_comp, E.map_comp, hψs, hψs, ← Category.assoc,
          show E.map (tr N.obj (e₀.βmono h)) = E.map (T.map (homOfLE (e₀.βmono h)).op) from rfl,
          hv', Category.assoc, Category.assoc,
          show E.map (tr P h) = tr (P ⋙ E) h from rfl]
        exact congrArg ((v _).inv ≫ ·) (e₀.ψnat h)
      ψφ := by
        intro m
        refine hext ?_
        rw [E.map_comp, hφs, hψs, Category.assoc, Iso.hom_inv_id_assoc]
        exact e₀.ψφ m
      φψ := by
        intro m
        refine hext ?_
        rw [E.map_comp, hψs, hφs, Category.assoc, ← Category.assoc (e₀.ψ (e₀.α m)), e₀.φψ m,
          show tr Q (le_trans (e₀.αle m) (e₀.βle (e₀.α m))) =
            Q.map (homOfLE (le_trans (e₀.αle m) (e₀.βle (e₀.α m)))).op from rfl, hv,
          Iso.inv_hom_id_assoc]
        rfl }
  -- `𝒥^c` kills a quasi-coherent module whose global sections are killed by `I^c`
  have hann : ∀ (c : ℕ) (X : W.Modules) [X.IsQuasicoherent],
      (∀ a ∈ J.ideal ⟨⊤, isAffineOpen_top W⟩ ^ c, ∀ x : E.obj X, a • x = 0) →
        idealPowerMultiple J c X = ⊥ := by
    intro c X _ h
    have hsec : (J.ideal ⟨⊤, isAffineOpen_top W⟩) ^ c •
        (⊤ : Submodule Γ(W, ⊤) (E.obj X)) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      exact fun a ha x _ => h a ha x
    have h := affine_idealPowerMultiple_eq_bot (J.ideal ⟨⊤, isAffineOpen_top W⟩) c X hsec
    rwa [← hJ] at h
  refine ⟨N, e, σ, fun n => ?_, fun c hker₀ n => ?_, fun c hcok₀ n => ?_⟩
  · -- compatibility with `τ`
    refine hext ?_
    show E.map (τ.app _ ≫ φs n) = E.map (F.obj.map _ ≫ s (op n))
    rw [E.map_comp, E.map_comp, hs, hφs, ← Category.assoc]
    exact (congrArg (· ≫ (v (op n)).hom) (hσ₀ n)).trans (Category.assoc _ _ _)
  · -- the kernel
    refine idealPowerMultiple_kernel_obj_eq_bot_of_termwise J J σ c (fun n => ?_) n
    have : (N.obj.obj (op n)).IsCoherent := hT.1 n
    have : (kernel (σ.hom.app (op n))).IsCoherent :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_kernel _
    have : (kernel (σ.hom.app (op n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
    have : PreservesFiniteLimits E :=
      _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits W.ringCatSheaf (op ⊤)
    have hinj : Function.Injective (E.map (kernel.ι (σ.hom.app (op n)))).hom :=
      (ModuleCat.mono_iff_injective _).mp (E.map_mono _)
    refine hann c _ fun a ha x => hinj ?_
    rw [map_smul, map_zero]
    refine hker₀ n a ha _ ((v (op n)).toLinearEquiv.injective ?_)
    have h0 := congrArg (fun g => (E.map g).hom x) (kernel.condition (σ.hom.app (op n)))
    simp only [Functor.map_comp, hσE, Functor.map_zero, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h0
    rw [map_zero]
    exact h0
  · -- the cokernel
    refine idealPowerMultiple_cokernel_obj_eq_bot_of_termwise J J σ c (fun n => ?_) n
    have : (T.obj (op n)).IsCoherent := hT.1 n
    have : (cokernel (σ.hom.app (op n))).IsCoherent :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel _
    have : (cokernel (σ.hom.app (op n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
    have hsurj := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen W
      (cokernel.π (σ.hom.app (op n))) ⊤ (isAffineOpen_top W)
    refine hann c _ fun a ha y => ?_
    obtain ⟨t, rfl⟩ : ∃ t : E.obj (N.obj.obj (op n)),
        (E.map (cokernel.π (σ.hom.app (op n)))).hom t = y := hsurj y
    obtain ⟨r, hr⟩ := hcok₀ n a ha ((v (op n)).inv.hom t)
    have ht : a • t = (E.map (σ.hom.app (op n))).hom r := by
      rw [hσE, ModuleCat.hom_comp, LinearMap.comp_apply, hr, map_smul]
      exact (congrArg (a • ·) (((v (op n)).inv_hom_id_apply t))).symm
    refine (map_smul (E.map (cokernel.π (σ.hom.app (op n)))).hom a t).symm.trans ?_
    rw [ht, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

end Stacks.Coherent

end
