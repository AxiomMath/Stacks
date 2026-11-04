module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# The Mittag-Leffler condition for the homology of an adic complex

Let `I` be an ideal of a Noetherian ring `A` and let `K →α L →β M` be a three-term complex of
finite `A`-modules. Reducing it modulo `Iⁿ` gives, in the middle degree, the subquotient

`H⁰(L/IⁿL) = β⁻¹(IⁿM) / (im α + IⁿL)`,

and these assemble into an inverse system over `n` whose transition maps are induced by the
inclusions `Iⁿ⁺¹ ⊆ Iⁿ`. This file names that system and proves that it satisfies the
Mittag-Leffler condition of Stacks 02N0.

The mathematics is the Artin--Rees comparison of Stacks 0EGU, which is proved in
`StacksFrontier.RingTheory.Module.AdicSystem.Homology`: that lemma produces, with a *uniform*
shift `c`, the comparison maps from `H = ker β / im α` to each level together with the equality
`Im(H⁰(L/Iⁿ⁺ᶜL) → H⁰(L/IⁿL)) = Im(H → H⁰(L/IⁿL))`. The images of the transition maps into level
`n` are therefore all equal to the image of `H` from level `n + c` on, which is exactly the
stabilization Stacks 02N0 asks for. Nothing here reproves Artin--Rees.

## Main definitions

* `Stacks.AdicSystem.ArtinReesHomology.adicCycles`: the degree-zero cycles `β⁻¹(IⁿM)` of the
  complex reduced modulo `Iⁿ`.
* `Stacks.AdicSystem.ArtinReesHomology.adicBoundaries`: its degree-zero boundaries
  `im α + IⁿL`.
* `Stacks.AdicSystem.ArtinReesHomology.adicHomology`: the degree-zero homology
  `β⁻¹(IⁿM) / (im α + IⁿL)` of the complex reduced modulo `Iⁿ`.
* `Stacks.AdicSystem.ArtinReesHomology.adicHomologyMap`: its transition maps.
* `Stacks.AdicSystem.ArtinReesHomology.adicHomologySystem`: the inverse system
  `n ↦ H⁰(L/IⁿL)`.

## Main results

* `Stacks.AdicSystem.ArtinReesHomology.adicHomologySystem_map`: the transition map of the
  system between two arbitrary levels is `adicHomologyMap`.
* `Stacks.AdicSystem.ArtinReesHomology.isMittagLefflerCategorical_adicHomologySystem`: the
  system `n ↦ H⁰(L/IⁿL)` is Mittag-Leffler, the stabilized image being the image of
  `H = ker β / im α`.

## Implementation notes

The cycles, boundaries and homology are the concrete subquotient model that Stacks 0EGU uses,
written out as `abbrev`s so that the types produced by that lemma and the ones named here are
the same by unfolding. The transition maps are `Submodule.mapQ` of the inclusion of cycles, for
an arbitrary pair of levels `m ≤ n`; the one-step maps are what the system is built from, and
`adicHomologySystem_map` identifies the general transition map with `adicHomologyMap` by
induction.

## References

* [Stacks Project, Tag 0EGU](https://stacks.math.columbia.edu/tag/0EGU)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AdicSystem.ArtinReesHomology

universe v u

variable {A : Type u} [CommRing A] {K L M : Type v}
  [AddCommGroup K] [Module A K] [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]

/-- The degree-zero cycles of the three-term complex `K →α L →β M` reduced modulo `Iⁿ`: the
submodule `β⁻¹(IⁿM)` of `L`. -/
abbrev adicCycles (I : Ideal A) (β : L →ₗ[A] M) (n : ℕ) : Submodule A L :=
  (I ^ n • (⊤ : Submodule A M)).comap β

/-- The degree-zero boundaries of the three-term complex `K →α L →β M` reduced modulo `Iⁿ`: the
submodule `im α + IⁿL` of `L`. -/
abbrev adicBoundaries (I : Ideal A) (α : K →ₗ[A] L) (n : ℕ) : Submodule A L :=
  LinearMap.range α ⊔ I ^ n • (⊤ : Submodule A L)

/-- The degree-zero homology `H⁰(L/IⁿL) = β⁻¹(IⁿM) / (im α + IⁿL)` of the three-term complex
`K →α L →β M` reduced modulo `Iⁿ`. -/
abbrev adicHomology (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) : Type v :=
  adicCycles I β n ⧸ (adicBoundaries I α n).comap (adicCycles I β n).subtype

/-- The cycles decrease as the level grows: `β⁻¹(IⁿM) ⊆ β⁻¹(IᵐM)` for `m ≤ n`. -/
theorem adicCycles_mono (I : Ideal A) (β : L →ₗ[A] M) {m n : ℕ} (h : m ≤ n) :
    adicCycles I β n ≤ adicCycles I β m :=
  Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right h))

/-- The boundaries decrease as the level grows: `im α + IⁿL ⊆ im α + IᵐL` for `m ≤ n`. -/
theorem adicBoundaries_mono (I : Ideal A) (α : K →ₗ[A] L) {m n : ℕ} (h : m ≤ n) :
    adicBoundaries I α n ≤ adicBoundaries I α m :=
  sup_le_sup le_rfl (Submodule.smul_mono_left (Ideal.pow_le_pow_right h))

/-- The transition map `H⁰(L/IⁿL) → H⁰(L/IᵐL)` of the homology of the reduced complexes, for
`m ≤ n`: the map induced by the inclusion of cycles. -/
def adicHomologyMap (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) {m n : ℕ} (h : m ≤ n) :
    adicHomology I α β n →ₗ[A] adicHomology I α β m :=
  Submodule.mapQ _ _ ((adicCycles I β n).inclusion (adicCycles_mono I β h))
    (fun _ hx => adicBoundaries_mono I α h hx)

/-- The transition map `adicHomologyMap` sends the class of a cycle `x ∈ β⁻¹(IⁿM)` to the class
of `x` regarded as an element of `β⁻¹(IᵐM)`. -/
@[simp]
theorem adicHomologyMap_mk (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) {m n : ℕ} (h : m ≤ n)
    (x : adicCycles I β n) :
    adicHomologyMap I α β h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(x : L), adicCycles_mono I β h x.2⟩ :=
  rfl

/-- The inverse system `n ↦ H⁰(L/IⁿL)` of the degree-zero homology of the three-term complex
`K →α L →β M` reduced modulo the powers of `I`, with the canonical transition maps. -/
def adicHomologySystem (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  Functor.ofOpSequence (X := fun n => ModuleCat.of A (adicHomology I α β n))
    (fun n => ModuleCat.ofHom (adicHomologyMap I α β (Nat.le_succ n)))

/-- The transition map of `adicHomologySystem` from level `n + 1` to level `n` is
`adicHomologyMap`. -/
@[simp]
theorem adicHomologySystem_map_succ (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    (adicHomologySystem I α β).map (homOfLE (Nat.le_succ n)).op =
      ModuleCat.ofHom (adicHomologyMap I α β (Nat.le_succ n)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Two morphisms out of `H⁰(L/IⁿL)` are equal once they agree on classes of cycles. -/
private theorem hom_ext_mk (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) {n : ℕ}
    {N : ModuleCat.{v} A} {f g : ModuleCat.of A (adicHomology I α β n) ⟶ N}
    (h : ∀ y : adicCycles I β n,
      f.hom (Submodule.Quotient.mk y) = g.hom (Submodule.Quotient.mk y)) :
    f = g := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact h y

/-- The transition map of `adicHomologySystem` between two arbitrary levels is
`adicHomologyMap`. -/
theorem adicHomologySystem_map (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) {m n : ℕ}
    (h : m ≤ n) :
    (adicHomologySystem I α β).map (homOfLE h).op =
      ModuleCat.ofHom (adicHomologyMap I α β h) := by
  induction n, h using Nat.le_induction with
  | base =>
    have hid : (adicHomologySystem I α β).map (homOfLE (le_refl m)).op = 𝟙 _ := by
      have hone : (homOfLE (le_refl m)).op = 𝟙 (op m) := rfl
      rw [hone, CategoryTheory.Functor.map_id]
    exact hid.trans (hom_ext_mk I α β fun _ => rfl)
  | succ n hmn ih =>
    rw [inverseSystem_transition_comp (adicHomologySystem I α β) hmn (Nat.le_succ n),
      adicHomologySystem_map_succ, ih]
    exact hom_ext_mk I α β fun _ => rfl

/-- **The Mittag-Leffler condition for the homology of an adic complex.** Let `I` be an ideal of
a Noetherian ring `A` and let `K →α L →β M` be a three-term complex of finite `A`-modules. Then
the inverse system `n ↦ H⁰(L/IⁿL)` of the degree-zero homology of the reduced complexes
satisfies the Mittag-Leffler condition of Stacks 02N0.

This is the Artin--Rees comparison of Stacks 0EGU read as a statement about transition images:
that lemma supplies a uniform shift `c` and comparison maps `H → H⁰(L/IⁿL)` out of
`H = ker β / im α` with `Im(H⁰(L/Iⁿ⁺ᶜL) → H⁰(L/IⁿL)) = Im(H → H⁰(L/IⁿL))`, and the comparison
maps are compatible with the transition maps, so every transition image into level `n` from
level `≥ n + c` is that same image of `H`. -/
theorem isMittagLefflerCategorical_adicHomologySystem [Module.Finite A K] [Module.Finite A L]
    [Module.Finite A M] [IsNoetherianRing A] (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (hcomplex : β.comp α = 0) :
    IsMittagLefflerCategorical (adicHomologySystem I α β) := by
  obtain ⟨toLevel, transition, _quotTransition, _fromQuotient, _htoLevel, htransition, _hquot,
    hcompat, _hfrom, c, _hcpos, _back, _hback₁, _hback₂, _hproiso, _hlim, _hml, hrange, _hrest⟩ :=
    exists_uniform_adic_homology_comparison I α β hcomplex
  -- The transition maps supplied by Stacks 0EGU are the ones `adicHomologySystem` is built
  -- from: both send the class of a cycle to the class of the same element of `L`.
  have htr : ∀ n : ℕ, ModuleCat.ofHom (transition n) =
      ModuleCat.ofHom (adicHomologyMap I α β (Nat.le_succ n)) := by
    intro n
    refine hom_ext_mk I α β fun y => ?_
    show transition n (Submodule.Quotient.mk y) = _
    rw [htransition n y ⟨(y : L), adicCycles_mono I β (Nat.le_succ n) y.2⟩ rfl]
    rfl
  -- Hence `adicHomologySystem` is the inverse system of Stacks 0EGU, where the Artin--Rees
  -- equality of images lives.
  have hsys : adicHomologySystem I α β =
      Functor.ofOpSequence (X := fun k => ModuleCat.of A (adicHomology I α β k))
        (fun k => ModuleCat.ofHom (transition k)) := by
    show Functor.ofOpSequence (X := fun k => ModuleCat.of A (adicHomology I α β k))
      (fun k => ModuleCat.ofHom (adicHomologyMap I α β (Nat.le_succ k))) = _
    congr 1
    funext k
    exact (htr k).symm
  rw [hsys]
  -- The comparison maps out of `H` factor through every level, by compatibility of the
  -- comparison with the one-step transition maps.
  have hfactor : ∀ (i k : ℕ) (h : i ≤ k) (z : _),
      ((Functor.ofOpSequence (X := fun k => ModuleCat.of A (adicHomology I α β k))
          (fun k => ModuleCat.ofHom (transition k))).map (homOfLE h).op).hom (toLevel k z) =
        toLevel i z := by
    intro i k h z
    induction k, h using Nat.le_induction with
    | base =>
      have hone : (homOfLE (le_refl i)).op = 𝟙 (op i) := rfl
      rw [hone, CategoryTheory.Functor.map_id]
      rfl
    | succ k hik ih =>
      have hstep : transition k (toLevel (k + 1) z) = toLevel k z :=
        LinearMap.congr_fun (hcompat k) z
      rw [inverseSystem_transition_comp _ hik (Nat.le_succ k),
        Functor.ofOpSequence_map_homOfLE_succ]
      show ((Functor.ofOpSequence (X := fun k => ModuleCat.of A (adicHomology I α β k))
          (fun k => ModuleCat.ofHom (transition k))).map (homOfLE hik).op).hom
          (transition k (toLevel (k + 1) z)) = toLevel i z
      rw [hstep]
      exact ih
  refine isMittagLefflerCategorical_of_range_eq_submodule _ (fun i => i + c)
    (fun i => Nat.le_add_right i c) (fun i => LinearMap.range (toLevel i)) ?_
  intro i k hbk hik
  refine le_antisymm ?_ ?_
  · rw [inverseSystem_transition_comp _ (Nat.le_add_right i c) hbk, ModuleCat.hom_comp]
    exact le_trans (LinearMap.range_comp_le_range _ _) (le_of_eq (hrange i))
  · rintro _ ⟨z, rfl⟩
    exact ⟨toLevel k z, hfactor i k hik z⟩

end Stacks.AdicSystem.ArtinReesHomology

end
