module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# The cone of a map of locally bounded complexes of finite locally free modules

Let `Y` be a scheme and let `α : 𝓔₁^• ⟶ 𝓔₂^•` be a map of locally bounded complexes of finite
locally free `𝒪_Y`-modules. Since

  `C(α)^n = 𝓔₁^{n + 1} ⊕ 𝓔₂^n`

the cone is again a locally bounded complex of finite locally free modules, and where the two
complexes have constant ranks `ρ` and `σ` the cone has the constant ranks
`n ↦ ρ(n + 1) + σ(n)`. These are the two facts the proof of [Stacks, Tag 0F9F] uses when it says
"we see that `C(α)^•` is a locally bounded complex of finite locally free `𝒪_Y`-modules".

## Main results

* `Stacks.Chow.isFiniteLocallyFree_mappingCone_X`,
  `Stacks.Chow.isFiniteLocallyFreeOfRank_mappingCone_X` — the terms of the cone, without and
  with ranks.
* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_mappingCone` — the cone of a map of locally
  bounded complexes of finite locally free modules is one again.
* `Stacks.Chow.coneRank` — the rank function `n ↦ ρ(n + 1) + σ(n)` of the cone, as a finitely
  supported function.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X` — the same ranks for the
  termwise pullback of the cone, which is the form the classes of the cone are read at.

## Implementation notes

The local bound for the cone is read off the two given bounds on the intersection of the two
given opens, which is where `Stacks.BlowUpComplexes.isZero_restrictModules_of_le` enters. That a
restriction kills the biproduct of two modules it kills is `Stacks.Chow.isZero_obj_biprod`,
proved from `CategoryTheory.Limits.biprod.total` alone: restriction to an open subspace is
additive, but it is not known here to preserve binary biproducts, so
`CategoryTheory.Functor.isZero_obj_biproduct` does not apply.

The cone is written with a type ascription to `CochainComplex Y.Modules ℤ` in the statement of
`Stacks.Chow.isLocallyBoundedFiniteLocallyFree_mappingCone`: the predicate is stated for a
complex of modules on a ringed space, so without the ascription the category is a metavariable
when `CochainComplex.mappingCone` asks for `HomologicalComplex.HasHomotopyCofiber` and the
instance is not found.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An additive functor and a binary biproduct -/

/-- **An additive functor which kills two objects kills their biproduct.** The identity of
`M ⊞ N` is `fst ≫ inl + snd ≫ inr` (`CategoryTheory.Limits.biprod.total`), and the image of each
summand factors through a zero object, so the image of the identity is zero.

Unlike `CategoryTheory.Functor.isZero_obj_biproduct` this needs no preservation of biproducts,
which is what makes it usable for a restriction of sheaves of modules to an open subspace. -/
theorem isZero_obj_biprod {A B : Type*} [Category A] [Category B] [Preadditive A]
    [Preadditive B] (F : A ⥤ B) [F.Additive] {M N : A} [HasBinaryBiproduct M N]
    (hM : IsZero (F.obj M)) (hN : IsZero (F.obj N)) : IsZero (F.obj (M ⊞ N)) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hM.eq_zero_of_tgt (F.map biprod.fst), hN.eq_zero_of_tgt (F.map biprod.snd),
    zero_comp, zero_comp, add_zero]

/-! ### The terms of the cone -/

section Terms

variable {Y : Scheme.{u}} {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)

/-- **The degree-`n` term of the cone is `𝓔₁^{n + 1} ⊕ 𝓔₂^n`**, which is
`HomologicalComplex.homotopyCofiber.XIsoBiprod` read in the cochain convention. -/
def mappingConeXIsoBiprod (n : ℤ) :
    (CochainComplex.mappingCone α).X n ≅ P₁.X (n + 1) ⊞ P₂.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod α n (n + 1) (by simp)

/-- **A term of the cone of a map of complexes of finite locally free modules is finite locally
free**, being the biproduct of two such modules. -/
theorem isFiniteLocallyFree_mappingCone_X (n : ℤ)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P₁.X (n + 1)))
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P₂.X n)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((CochainComplex.mappingCone α).X n) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (mappingConeXIsoBiprod α n).symm
    (h := GenuineChern.isFiniteLocallyFree_of_shortExact _
      (ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.X (n + 1)) (P₂.X n)).shortExact h₁ h₂)

/-- **A term of the cone has the summed rank.** If `𝓔₁^{n + 1}` is finite locally free of rank
`a` and `𝓔₂^n` of rank `b`, then `C(α)^n` is finite locally free of rank `a + b`: it is their
biproduct, and a biproduct is a split extension. -/
theorem isFiniteLocallyFreeOfRank_mappingCone_X (n : ℤ) (a b : ℕ)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P₁.X (n + 1)) a)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P₂.X n) b) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((CochainComplex.mappingCone α).X n) (a + b) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (mappingConeXIsoBiprod α n).symm
    (GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
      (ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.X (n + 1)) (P₂.X n)).shortExact a b h₁ h₂)

/-- **The cone of a map of locally bounded complexes of finite locally free modules is one
again.** Each term is a biproduct of two finite locally free modules, and on the intersection of
two opens carrying bounds for the two complexes the terms of the cone restrict to zero outside
the shifted common range. -/
theorem isLocallyBoundedFiniteLocallyFree_mappingCone
    (h₁ : IsLocallyBoundedFiniteLocallyFree P₁)
    (h₂ : IsLocallyBoundedFiniteLocallyFree P₂) :
    IsLocallyBoundedFiniteLocallyFree
      ((CochainComplex.mappingCone α : CochainComplex Y.Modules ℤ)) := by
  refine ⟨fun n ↦ isFiniteLocallyFree_mappingCone_X α n (h₁.1 (n + 1)) (h₂.1 n), fun x ↦ ?_⟩
  obtain ⟨U₁, hx₁, lo₁, hi₁, hbd₁⟩ := h₁.2 x
  obtain ⟨U₂, hx₂, lo₂, hi₂, hbd₂⟩ := h₂.2 x
  refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, min (lo₁ - 1) lo₂, max (hi₁ - 1) hi₂, fun n hn ↦ ?_⟩
  have hn₁ : n + 1 < lo₁ ∨ hi₁ < n + 1 := by rcases hn with hn | hn <;> omega
  have hn₂ : n < lo₂ ∨ hi₂ < n := by rcases hn with hn | hn <;> omega
  refine IsZero.of_iso (isZero_obj_biprod _
    (Stacks.BlowUpComplexes.isZero_restrictModules_of_le inf_le_left _ (hbd₁ (n + 1) hn₁))
    (Stacks.BlowUpComplexes.isZero_restrictModules_of_le inf_le_right _ (hbd₂ n hn₂)))
    (Functor.mapIso _ (mappingConeXIsoBiprod α n))

end Terms

/-! ### The rank function of the cone -/

/-- **The rank function of the cone**, `n ↦ ρ(n + 1) + σ(n)`: the rank function of `C(α)^•` where
`𝓔₁^•` has the constant ranks `ρ` and `𝓔₂^•` the constant ranks `σ`. It is finitely supported,
being supported in the union of the shift of the support of `ρ` and the support of `σ`. -/
def coneRank (ρ σ : ℤ →₀ ℕ) : ℤ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun n ↦ ρ (n + 1) + σ n) (by
    classical
    refine Set.Finite.subset
      (((ρ.support.image fun m ↦ m - 1) ∪ σ.support).finite_toSet) fun n hn ↦ ?_
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe, Finsupp.mem_support_iff]
    by_contra hcon
    simp only [not_or, not_exists, not_and, not_not] at hcon
    exact hn (by
      rw [hcon.2]
      refine Nat.add_eq_zero.mpr ⟨?_, rfl⟩
      by_contra hρ
      exact absurd (by omega : n + 1 - 1 = n) (hcon.1 (n + 1) hρ)))

/-- The value of the cone's rank function. -/
@[simp]
theorem coneRank_apply (ρ σ : ℤ →₀ ℕ) (n : ℤ) : coneRank ρ σ n = ρ (n + 1) + σ n := rfl

/-- **A term of the cone has the rank the cone's rank function assigns to it.** -/
theorem isFiniteLocallyFreeOfRank_mappingCone_X_coneRank {Y : Scheme.{u}}
    {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂) (ρ σ : ℤ →₀ ℕ)
    (h₁ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P₁.X n) (ρ n))
    (h₂ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P₂.X n) (σ n)) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((CochainComplex.mappingCone α).X n) (coneRank ρ σ n) :=
  isFiniteLocallyFreeOfRank_mappingCone_X α n (ρ (n + 1)) (σ n) (h₁ (n + 1)) (h₂ n)

/-- **The ranks of the termwise pullback of the cone.** If the termwise pullbacks of the two
complexes have constant ranks `ρ` and `σ`, then the termwise pullback of the cone has the constant
ranks `n ↦ ρ(n + 1) + σ(n)`: the degree-`n` term of the cone is a biproduct, pulling back the
split short exact sequence it sits in leaves it split short exact, and the middle term of a split
extension of modules of constant ranks has the summed rank.

This is the form in which both the total Chern class and the alternating rank class of the cone
are read, since each is characterized by its restrictions along morphisms over which the complex
has constant ranks. -/
theorem isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X {Y Z : Scheme.{u}}
    {P₁ P₂ : CochainComplex Y.Modules ℤ} (g : Z ⟶ Y) (α : P₁ ⟶ P₂) (ρ σ : ℤ →₀ ℕ)
    (h₁ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P₁).X n) (ρ n))
    (h₂ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P₂).X n) (σ n)) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g (CochainComplex.mappingCone α :
        CochainComplex Y.Modules ℤ)).X n) (coneRank ρ σ n) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullback g).mapIso (mappingConeXIsoBiprod α n).symm)
    (GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
      (ShortComplex.mk ((Scheme.Modules.pullback g).map
          (biprod.inl : P₁.X (n + 1) ⟶ P₁.X (n + 1) ⊞ P₂.X n))
        ((Scheme.Modules.pullback g).map
          (biprod.snd : P₁.X (n + 1) ⊞ P₂.X n ⟶ P₂.X n))
        (by rw [← Functor.map_comp, biprod.inl_snd, Functor.map_zero]))
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.X (n + 1)) (P₂.X n)).map
        (Scheme.Modules.pullback g)).shortExact (ρ (n + 1)) (σ n) (h₁ (n + 1)) (h₂ n))

end Stacks.Chow

end
