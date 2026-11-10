module

public import Mathlib.RingTheory.Flat.Tensor
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Tensoring a short exact sequence with flat quotient

For a short exact sequence `0 → F'' → F' → F → 0` of modules over a commutative ring whose
quotient `F` is flat, tensoring with any module `G` gives a short exact sequence
`0 → F'' ⊗ G → F' ⊗ G → F ⊗ G → 0`. Injectivity of the first map is proved with character
modules: flatness of `F` makes the character-module dual of `F'' → F'` a split surjection.

## Main results

* `tensor_flat_quotient_shortExact`: tensoring a short exact sequence whose quotient is flat
  with any module gives a short exact sequence.
* `dual_map_split_of_flat`: if the quotient is flat, the character-module dual of the injection
  has a linear section.
* `dual_lTensor_surjective_of_postcomp`: surjectivity of postcomposition with
  `CharacterModule.dual a` implies surjectivity of `CharacterModule.dual (LinearMap.lTensor G a)`.

## References

* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

open LinearMap TensorProduct CharacterModule

/-- `LinearMap.rTensor M f` is injective if and only if `LinearMap.lTensor M f` is injective. -/
theorem rTensor_injective_iff_lTensor
    {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : N →ₗ[R] P) :
    Function.Injective (LinearMap.rTensor M f) ↔ Function.Injective (LinearMap.lTensor M f) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj M f).symm

/-- If `0 → F'' → F' → F → 0` is a short exact sequence of `R`-modules with `F` flat, then the
character-module dual `CharacterModule.dual a` of the injection `a : F'' → F'` has a linear
section. -/
theorem dual_map_split_of_flat
    {R : Type*} [CommRing R]
    {F'' F' F : Type*} [AddCommGroup F''] [AddCommGroup F'] [AddCommGroup F]
    [Module R F''] [Module R F'] [Module R F]
    (a : F'' →ₗ[R] F') (b : F' →ₗ[R] F)
    (ha : Function.Injective a) (hexact : Function.Exact a b)
    (hb : Function.Surjective b) (hFflat : Module.Flat R F) :
    ∃ s : CharacterModule F'' →ₗ[R] CharacterModule F',
      CharacterModule.dual a ∘ₗ s = LinearMap.id := by
  have hbaer : Module.Baer R (CharacterModule F) :=
    Module.Flat.iff_characterModule_baer.mp hFflat
  have hdual_exact : Function.Exact (CharacterModule.dual b) (CharacterModule.dual a) := by
    rw [LinearMap.exact_iff]
    refine le_antisymm (fun χ hχ => ?_) ?_
    · rw [LinearMap.mem_ker] at hχ
      have hrinv : Function.RightInverse (Function.surjInv hb) ⇑b.toAddMonoidHom :=
        Function.rightInverse_surjInv hb
      have hker : b.toAddMonoidHom.ker ≤ χ.ker := by
        intro x hx
        rw [AddMonoidHom.mem_ker] at hx ⊢
        obtain ⟨y, rfl⟩ : x ∈ LinearMap.range a := by
          rwa [← hexact.linearMap_ker_eq, LinearMap.mem_ker]
        have hthis := DFunLike.congr_fun hχ y
        rwa [CharacterModule.dual_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddMonoidHom.zero_apply] at hthis
      refine ⟨b.toAddMonoidHom.liftOfRightInverse (Function.surjInv hb) hrinv ⟨χ, hker⟩, ?_⟩
      ext x
      exact AddMonoidHom.liftOfRightInverse_comp_apply b.toAddMonoidHom _ hrinv ⟨χ, hker⟩ x
    · rintro χ ⟨ψ, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← CharacterModule.dual_comp,
        hexact.linearMap_comp_eq_zero]
      simp
  have hdb_inj : Function.Injective (CharacterModule.dual b) :=
    CharacterModule.dual_injective_iff_surjective.mpr hb
  obtain ⟨r, hr⟩ := hbaer.extension_property (CharacterModule.dual b) hdb_inj LinearMap.id
  have hretr : ∃ l, l ∘ₗ CharacterModule.dual b = LinearMap.id := ⟨r, hr⟩
  exact ((hdual_exact.split_tfae hdb_inj
    (CharacterModule.dual_surjective_iff_injective.mpr ha)).out 2 1).mp hretr

/-- If postcomposition with `CharacterModule.dual a` is surjective as a map
`(G →ₗ[R] CharacterModule F') → (G →ₗ[R] CharacterModule F'')`, then the dual map
`CharacterModule.dual (LinearMap.lTensor G a)` is surjective. -/
theorem dual_lTensor_surjective_of_postcomp
    {R : Type*} [CommRing R]
    {F'' F' : Type*} [AddCommGroup F''] [AddCommGroup F']
    [Module R F''] [Module R F'] (a : F'' →ₗ[R] F')
    (G : Type*) [AddCommGroup G] [Module R G]
    (hsurj : ∀ ξ : G →ₗ[R] CharacterModule F'',
      ∃ η : G →ₗ[R] CharacterModule F', CharacterModule.dual a ∘ₗ η = ξ) :
    Function.Surjective (CharacterModule.dual (LinearMap.lTensor G a)) := by
  have hsq : ∀ η : G →ₗ[R] CharacterModule F',
      CharacterModule.dual (LinearMap.lTensor G a) (CharacterModule.homEquiv η)
        = CharacterModule.homEquiv (CharacterModule.dual a ∘ₗ η) := by
    intro η
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul g m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro χ
  obtain ⟨η, hη⟩ := hsurj (CharacterModule.homEquiv.symm χ)
  exact ⟨CharacterModule.homEquiv η, by rw [hsq η, hη, LinearEquiv.apply_symm_apply]⟩

/-- Let `0 → F'' → F' → F → 0` be a short exact sequence of modules over a commutative ring `R`:
`a : F'' → F'` is injective, the sequence is exact at `F'` and `b : F' → F` is surjective. If `F`
is flat, then for every `R`-module `G` the tensored sequence `0 → F'' ⊗ G → F' ⊗ G → F ⊗ G → 0`
is short exact: `a ⊗ 1` is injective, the sequence is exact at `F' ⊗ G`, and `b ⊗ 1` is
surjective. -/
@[stacks 00HL,
  ega "0 6.1.2" "exactness",
  sga "1 IV 1.1" "(i)",
  ega "IV 2.1.8" "(i), affine case",
  ega "0 15.1.17" "more general",
  ega "IV 2.1.10" "special case",
  sga "3 III 4.6.4" "more general",
  sga "4 XVII 4.1.1" "(ii), special case"]
theorem tensor_flat_quotient_shortExact
    {R : Type*} [CommRing R]
    {F'' F' F : Type*} [AddCommGroup F''] [AddCommGroup F'] [AddCommGroup F]
    [Module R F''] [Module R F'] [Module R F]
    (a : F'' →ₗ[R] F') (b : F' →ₗ[R] F)
    (ha : Function.Injective a) (hexact : Function.Exact a b)
    (hb : Function.Surjective b)
    (hFflat : Module.Flat R F)
    (G : Type*) [AddCommGroup G] [Module R G] :
    Function.Injective (LinearMap.rTensor G a) ∧
      Function.Exact (LinearMap.rTensor G a) (LinearMap.rTensor G b) ∧
      Function.Surjective (LinearMap.rTensor G b) := by
  refine ⟨?_, rTensor_exact G hexact hb, LinearMap.rTensor_surjective G hb⟩
  rw [rTensor_injective_iff_lTensor, ← CharacterModule.dual_surjective_iff_injective]
  obtain ⟨s, hs⟩ := dual_map_split_of_flat a b ha hexact hb hFflat
  exact dual_lTensor_surjective_of_postcomp a G fun ξ =>
    ⟨s ∘ₗ ξ, by rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]⟩
