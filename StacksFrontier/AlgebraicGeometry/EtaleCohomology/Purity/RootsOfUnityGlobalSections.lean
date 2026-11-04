module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport

/-!
# Global sections of `μ_ℓ` on a scheme whose global functions form a domain

Let `X` be a scheme on which `ℓ` is invertible. The Kummer sequence identifies `H⁰(X, μ_ℓ)` with
the `ℓ`-torsion of `H⁰(X, 𝐆_m) = Γ(X, 𝒪_X)^×`, i.e. with the group of `ℓ`-th roots of unity in
`Γ(X, 𝒪_X)`. When `Γ(X, 𝒪_X)` is a domain containing a primitive `ℓ`-th root of unity this group
has exactly `ℓ` elements.

## Main results

* `Stacks.EtaleCohomology.Purity.natCard_sheafH_zero_rootsOfUnity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

/-- The `n`-torsion of `Additive Rˣ` is the group of `n`-th roots of unity of `R`. -/
theorem natCard_nsmul_eq_zero_units {R : Type*} [CommRing R] (n : ℕ) :
    Nat.card {x : Additive Rˣ // n • x = 0} = Nat.card (rootsOfUnity n R) := by
  refine Nat.card_congr ⟨fun x => ⟨Additive.toMul x.1, ?_⟩, fun y => ⟨Additive.ofMul y.1, ?_⟩,
    fun x => rfl, fun y => rfl⟩
  · have := congrArg Additive.toMul x.2
    rwa [toMul_nsmul, toMul_zero] at this
  · exact y.2

variable (X : Scheme.{u}) {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (hX : IsUnit ((ℓ : ℕ) : Γ(X, ⊤)))

include hℓ0 hX in
/-- **`H⁰(X, μ_ℓ)` is the group of `ℓ`-th roots of unity in `Γ(X, 𝒪_X)`**, in cardinality. -/
theorem natCard_sheafH_zero_rootsOfUnity_eq :
    Nat.card (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X ℓ) 0) =
      Nat.card (rootsOfUnity ℓ Γ(X, ⊤)) := by
  have hinj : Function.Injective
      (Sheaf.H.map.{u + 1} (Stacks.Kummer.rootsOfUnityι.{u, 0} X ℓ) 0) :=
    fun a b h => Abelian.Ext.postcomp_mk₀_injective_of_mono _
      (Stacks.Kummer.rootsOfUnityι.{u, 0} X ℓ) h
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  let E : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} X) 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
    (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, 0} X) hT).trans AddEquiv.ulift
  let pw := Sheaf.H.map.{u + 1} (Stacks.Kummer.powMap.{u, 0} X ℓ) 0
  have hE : ∀ y, E (pw y) = ℓ • E y := by
    intro y
    obtain ⟨a, ha⟩ := Stacks.Kummer.ofUnit_surjective
      (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, 0} X) hT y)
    show (Sheaf.H.equiv₀ _ hT (pw y)).down = ℓ • (Sheaf.H.equiv₀ _ hT y).down
    rw [← Sheaf.H.equiv₀_naturality, ← ha, Stacks.Kummer.powMap_app_ofUnit]
    show Additive.ofMul (a ^ ℓ) = ℓ • Additive.ofMul a
    rw [ofMul_pow]
  have hrange : ∀ y, y ∈ (Sheaf.H.map.{u + 1} (Stacks.Kummer.rootsOfUnityι.{u, 0} X ℓ) 0).range ↔
      ℓ • E y = 0 := by
    intro y
    rw [Stacks.Kummer.mem_range_sheafH_map_rootsOfUnityι_iff.{u + 1, u, 0} X hℓ0 hX 0 y, ← hE,
      AddEquiv.map_eq_zero_iff]
  rw [← natCard_nsmul_eq_zero_units]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨E (Sheaf.H.map.{u + 1} (Stacks.Kummer.rootsOfUnityι.{u, 0} X ℓ) 0 x),
      (hrange _).1 ⟨x, rfl⟩⟩) ⟨fun a b h => hinj (E.injective (congrArg Subtype.val h)),
      fun z => ?_⟩)
  obtain ⟨x, hx⟩ := (hrange (E.symm z.1)).2 (by simpa using z.2)
  exact ⟨x, Subtype.ext (by simp [hx])⟩

include hℓ0 hX in
/-- **`H⁰(X, μ_ℓ)` has exactly `ℓ` elements** when `Γ(X, 𝒪_X)` is a domain containing a primitive
`ℓ`-th root of unity. -/
theorem natCard_sheafH_zero_rootsOfUnity [IsDomain Γ(X, ⊤)] {ζ : Γ(X, ⊤)}
    (hζ : IsPrimitiveRoot ζ ℓ) :
    Nat.card (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X ℓ) 0) = ℓ := by
  have : NeZero ℓ := ⟨hℓ0⟩
  rw [natCard_sheafH_zero_rootsOfUnity_eq X hℓ0 hX, hζ.card_rootsOfUnity]

end Stacks.EtaleCohomology.Purity

end
