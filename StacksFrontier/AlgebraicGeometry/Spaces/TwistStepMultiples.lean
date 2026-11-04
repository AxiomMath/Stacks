module

public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent

/-!
# Twists by multiples of a fixed exponent

Let `𝓛` be an invertible sheaf of modules on a ringed site.  Twisting twice is twisting once by
the sum of the exponents: `(𝓕 ⊗ 𝓛^{⊗ n}) ⊗ 𝓛^{⊗ m} ≅ 𝓕 ⊗ 𝓛^{⊗ (n + m)}` for `m ≥ 0`.

On an algebraic space `X` this gives the reduction used in the proof of Stacks 0D2W: if every
coherent `𝒪_X`-module `𝓕` has some twist `𝓕 ⊗ 𝓛^{⊗ n}`, `n ≥ 1`, with vanishing `H¹`, then for
every `d ≥ 1` every coherent `𝓕` has a twist `𝓕 ⊗ 𝓛^{⊗ ad}` by a multiple of `d` with vanishing
`H¹`.  Apply the hypothesis to the coherent module `⨁_{i < d} 𝓕 ⊗ 𝓛^{⊗ i}`: its `n`-th twist is
`⨁_{i < d} 𝓕 ⊗ 𝓛^{⊗ (i + n)}`, and one of the exponents `i + n` is a multiple of `d`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorSheafTensorPowerIso`: the isomorphism
  `(𝓕 ⊗ 𝓛^{⊗ n}) ⊗ 𝓛^{⊗ m} ≅ 𝓕 ⊗ 𝓛^{⊗ (n + m)}`, `m : ℕ`.
* `AlgebraicGeometry.Space.twistStepAddIso`: the same for `AlgebraicGeometry.Space.twistStep`.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_obj_twistStep_mul`: twists by multiples of `d` killed by
  a functor such as `H¹(X, -)`, from twists killed by it.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L]

/-- **Twisting twice is twisting by the sum**: `(𝓕 ⊗ 𝓛^{⊗ n}) ⊗ 𝓛^{⊗ m} ≅ 𝓕 ⊗ 𝓛^{⊗ (n + m)}`
for a natural number `m`, by induction on `m` from the associator and the successor comparison
`𝓛^{⊗ k} ⊗ 𝓛 ≅ 𝓛^{⊗ (k + 1)}`. -/
noncomputable def tensorSheafTensorPowerIso
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (n : ℤ) : (m : ℕ) →
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).obj
          (tensorPower O hO L n))).obj (tensorPower O hO L m) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).obj
        (tensorPower O hO L (n + m)))
  | 0 => tensorProductRightUnitor O hO _ ≪≫
      tensorProductIso O hO (Iso.refl F) (tensorPowerReindex O hO L (by simp))
  | m + 1 =>
      tensorProductIso O hO (Iso.refl _)
          ((tensorPowerSuccIso O hO L m).symm ≪≫
            tensorProductIso O hO (tensorPowerReindex O hO L rfl) (Iso.refl L)) ≪≫
        (tensorProductAssociator O hO _ _ _).symm ≪≫
        tensorProductIso O hO (tensorSheafTensorPowerIso F n m) (Iso.refl L) ≪≫
        tensorProductAssociator O hO _ _ _ ≪≫
        tensorProductIso O hO (Iso.refl F)
          (tensorPowerSuccIso O hO L (n + m) ≪≫ tensorPowerReindex O hO L (by push_cast; ring))

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Twisting twice is twisting by the sum**, for the twisting steps of an algebraic space. -/
noncomputable def twistStepAddIso (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (m : ℕ) (n : ℤ) (F : Modules.{u, u} B S hS X.1 X.2) :
    twistStep B S hS X.1 X.2 L m (twistStep B S hS X.1 X.2 L n F) ≅
      twistStep B S hS X.1 X.2 L (n + m) F :=
  @Stacks.SheafOfModules.Invertible.tensorSheafTensorPowerIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›) F n m

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **Twists by multiples of `d` with vanishing cohomology.**  Let `H` be a functor out of the
`𝒪_X`-modules of a locally Noetherian algebraic space, for instance `H¹(X, -)`.  If every
coherent `𝓕` has a twist `𝓕 ⊗ 𝓛^{⊗ n}`, `n ≥ 1`, killed by `H`, then for every `d ≥ 1` every
coherent `𝓕` has a twist `𝓕 ⊗ 𝓛^{⊗ ad}` killed by `H`.

The hypothesis at `⨁_{i < d} 𝓕 ⊗ 𝓛^{⊗ i}` gives an `n` killing its `n`-th twist; each
`𝓕 ⊗ 𝓛^{⊗ (i + n)}` is the `n`-th twist of a summand, hence a retract of that twist, and one of
the exponents `i + n` is a multiple of `d`. -/
theorem exists_isZero_obj_twistStep_mul (X : AlgebraicSpaces B S hS)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    {D : Type*} [Category D] [HasZeroMorphisms D] (H : Modules.{u, u} B S hS X.1 X.2 ⥤ D)
    (h : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      ∃ n : ℕ, 1 ≤ n ∧ IsZero (H.obj (twistStep B S hS X.1 X.2 L n F)))
    (d : ℕ) (hd : 0 < d) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) :
    ∃ a : ℕ, IsZero (H.obj (twistStep B S hS X.1 X.2 L ((a * d : ℕ) : ℤ) F)) := by
  let f : Fin d → Modules.{u, u} B S hS X.1 X.2 := fun i => twistStep B S hS X.1 X.2 L i F
  have hf : ∀ i, IsCoherent B S hS X.1 X.2 (f i) := fun i =>
    have := isCoherentOnSite_twistStep B S hS X.1 X.2 L i F hF.toIsCoherentOnSite
    isCoherent_of_isCoherentOnSite B S hS X.1 X.2 _
  obtain ⟨n, -, hz⟩ := h (⨁ f) (isCoherent_biproduct B S hS X.1 X.2 f hf)
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
    (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›) n)
  let G : Modules.{u, u} B S hS X.1 X.2 ⥤ D := T ⋙ H
  -- each summand's twist is a retract of the twist of the sum
  have hsummand : ∀ i, IsZero (G.obj (f i)) := by
    intro i
    have hz' : IsZero (G.obj (⨁ f)) := hz
    rw [IsZero.iff_id_eq_zero]
    have : 𝟙 (G.obj (f i)) = G.map (biproduct.ι f i) ≫ G.map (biproduct.π f i) := by
      rw [← G.map_comp, biproduct.ι_π_self, G.map_id]
    rw [this, hz'.eq_of_tgt (G.map (biproduct.ι f i)) 0, zero_comp]
  -- the exponent `i + n` that is a multiple of `d`
  let i : Fin d := ⟨(d - n % d) % d, Nat.mod_lt _ hd⟩
  have hdvd : d ∣ (i : ℕ) + n := by
    rw [Nat.dvd_iff_mod_eq_zero]
    show ((d - n % d) % d + n) % d = 0
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← Nat.sub_add_comm (Nat.mod_lt n hd).le,
      Nat.add_sub_assoc (Nat.mod_le n d), Nat.add_mod_left]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub_mod n)
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, ?_⟩
  have hcast : ((i : ℕ) : ℤ) + (n : ℤ) = ((a * d : ℕ) : ℤ) := by
    rw [← Nat.cast_add, ha, Nat.mul_comm]
  rw [← hcast]
  exact (hsummand i).of_iso (H.mapIso (twistStepAddIso X L n (i : ℤ) F)).symm

end AlgebraicGeometry.Space

end
