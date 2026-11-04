module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves

/-!
# Adic quotients along a surjection

Let `h : R → S` be a surjective ring homomorphism, `𝔞 ⊆ R` an ideal and `𝔟 = h(𝔞) S` its image.
If the kernel of `h` is contained in `𝔞ʲ`, then `h` induces an isomorphism of `R`-modules
`R/𝔞ʲ ≅ S/𝔟ʲ`, the target read over `R`. These isomorphisms are compatible with the transition
maps of the two adic quotient systems `j ↦ R/𝔞ʲ` and `j ↦ S/𝔟ʲ`.

For `R = Λ`, `S = Λ/Iⁿ` and `h` the quotient map, this identifies the quotients `Λ/Iʲ`,
`j ≤ n`, with the quotients of the single ring `Λ/Iⁿ`; for `R` the `I`-adic completion of a
Noetherian ring `Λ` and `h` the evaluation at level `n`, it does the same for the completion.

## Main definitions

* `AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso`: the isomorphism
  `R/𝔞ʲ ≅ S/𝔟ʲ` of `R`-modules.

## Main results

* `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem_map`: the transition maps of
  `n ↦ M/IⁿM` are Mathlib's `AdicCompletion.transitionMap`.
* `AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso_naturality`: compatibility with
  the transition maps of the adic quotient systems.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.ProEtale

/-- The transition maps of the tower `n ↦ M/IⁿM` are Mathlib's `AdicCompletion.transitionMap`. -/
theorem adicQuotientModuleSystem_map {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{v} A)
    {m n : ℕ} (h : m ≤ n) :
    (adicQuotientModuleSystem A I M).map (homOfLE h).op =
      ModuleCat.ofHom (AdicCompletion.transitionMap I M h) := by
  induction h
  on_goal 1 =>
    rw [show (homOfLE (le_refl m)).op = 𝟙 (Opposite.op m) from rfl, CategoryTheory.Functor.map_id]
  on_goal 2 =>
    rename_i n h ih
    rw [show (homOfLE (Nat.le_succ_of_le h)).op =
      (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op from rfl, Functor.map_comp, ih]
    dsimp only [adicQuotientModuleSystem]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  all_goals
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

variable {R S : Type v} [CommRing R] [CommRing S] (h : R →+* S) (hh : Function.Surjective h)
  (𝔞 : Ideal R) (𝔟 : Ideal S) (h𝔟 : 𝔞.map h = 𝔟)

/-- The `R`-linear map `R/𝔞ʲ → S/𝔟ʲ` induced by `h`, the target read over `R`. -/
def adicQuotientRestrictScalarsHom (j : ℕ) :
    (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R)).obj (op j) ⟶
      (ModuleCat.restrictScalars h).obj
        ((adicQuotientModuleSystem S 𝔟 (ModuleCat.of S S)).obj (op j)) :=
  ModuleCat.semilinearMapAddEquiv h _ _ <|
    Submodule.mapQ (𝔞 ^ j • ⊤ : Submodule R R) (𝔟 ^ j • ⊤ : Submodule S S)
      ({ toFun := h, map_add' := h.map_add, map_smul' := h.map_mul } : R →ₛₗ[h] S)
      (by
        intro r hr
        have hr' : r ∈ 𝔞 ^ j := by simpa using hr
        have : h r ∈ 𝔟 ^ j := by
          rw [← h𝔟, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem h hr'
        simpa using this)

/-- The map `R/𝔞ʲ → S/𝔟ʲ` sends the class of `r` to the class of `h r`. -/
theorem adicQuotientRestrictScalarsHom_mk (j : ℕ) (r : R) :
    (adicQuotientRestrictScalarsHom h 𝔞 𝔟 h𝔟 j).hom (Submodule.Quotient.mk r) =
      (Submodule.Quotient.mk (h r) : S ⧸ (𝔟 ^ j • ⊤ : Submodule S S)) :=
  rfl

include hh in
/-- If `h` is surjective and its kernel is contained in `𝔞ʲ`, then the map `R/𝔞ʲ → S/𝔟ʲ`
induced by `h` is bijective. -/
theorem bijective_adicQuotientRestrictScalarsHom (j : ℕ) (hj : RingHom.ker h ≤ 𝔞 ^ j) :
    Function.Bijective (adicQuotientRestrictScalarsHom h 𝔞 𝔟 h𝔟 j).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk (h r) : S ⧸ (𝔟 ^ j • ⊤ : Submodule S S)) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    have hx' : h r ∈ (𝔞 ^ j).map h := by
      rw [Ideal.map_pow, h𝔟]
      simpa using hx
    obtain ⟨y, hy, hyr⟩ := (Ideal.mem_map_iff_of_surjective h hh).1 hx'
    show (Submodule.Quotient.mk r : R ⧸ (𝔞 ^ j • ⊤ : Submodule R R)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hker : r - y ∈ 𝔞 ^ j := hj (by rw [RingHom.mem_ker, map_sub, hyr, sub_self])
    simpa using (𝔞 ^ j).add_mem hker hy
  · intro x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨r, rfl⟩ := hh s
    exact ⟨Submodule.Quotient.mk r, adicQuotientRestrictScalarsHom_mk h 𝔞 𝔟 h𝔟 j r⟩

/-- **Adic quotients along a surjection.** If `h : R → S` is surjective, `𝔟 = h(𝔞) S` and the
kernel of `h` is contained in `𝔞ʲ`, then `h` induces an isomorphism of `R`-modules
`R/𝔞ʲ ≅ S/𝔟ʲ`. -/
def adicQuotientRestrictScalarsIso (j : ℕ) (hj : RingHom.ker h ≤ 𝔞 ^ j) :
    (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R)).obj (op j) ≅
      (ModuleCat.restrictScalars h).obj
        ((adicQuotientModuleSystem S 𝔟 (ModuleCat.of S S)).obj (op j)) :=
  (LinearEquiv.ofBijective _
    (bijective_adicQuotientRestrictScalarsHom h hh 𝔞 𝔟 h𝔟 j hj)).toModuleIso

/-- The forward map of the isomorphism `R/𝔞ʲ ≅ S/𝔟ʲ` is `adicQuotientRestrictScalarsHom`. -/
@[simp]
theorem adicQuotientRestrictScalarsIso_hom (j : ℕ) (hj : RingHom.ker h ≤ 𝔞 ^ j) :
    (adicQuotientRestrictScalarsIso h hh 𝔞 𝔟 h𝔟 j hj).hom =
      adicQuotientRestrictScalarsHom h 𝔞 𝔟 h𝔟 j :=
  rfl

/-- The isomorphisms `R/𝔞ʲ ≅ S/𝔟ʲ` are compatible with the transition maps. -/
theorem adicQuotientRestrictScalarsIso_naturality {i j : ℕ} (hij : i ≤ j)
    (hi : RingHom.ker h ≤ 𝔞 ^ i) (hj : RingHom.ker h ≤ 𝔞 ^ j) :
    (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R)).map (homOfLE hij).op ≫
        (adicQuotientRestrictScalarsIso h hh 𝔞 𝔟 h𝔟 i hi).hom =
      (adicQuotientRestrictScalarsIso h hh 𝔞 𝔟 h𝔟 j hj).hom ≫
        (ModuleCat.restrictScalars h).map
          ((adicQuotientModuleSystem S 𝔟 (ModuleCat.of S S)).map (homOfLE hij).op) := by
  rw [adicQuotientModuleSystem_map, adicQuotientModuleSystem_map]
  ext x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end AlgebraicGeometry.ProEtale

end
