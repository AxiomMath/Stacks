module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalMember
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingCut

/-!
# Properties of a general member of a finite dimensional vector space

For a finite dimensional vector space `V` over a field `k`, a property `P` of vectors holds for a
*general* `k`-rational member, `AlgebraicGeometry.GoodNeighbourhood.GeneralIn k V P`, if it holds
at every vector `Σ aⱼ bⱼ` (`b` the chosen basis `Module.finBasis k V`) whose coordinate tuple `a`
is a `k`-point of a fixed nonempty open of the parameter space `𝔸^{dim V}_k` and which avoids
finitely many hyperplanes. This is the form in which the Bertini theorems
([Stacks, Tag 0FD6]) are combined: finitely many general properties hold at once
(`AlgebraicGeometry.GoodNeighbourhood.GeneralIn.and`), the parameter space being irreducible,
and over an infinite field a general property holds for some vector
(`AlgebraicGeometry.GoodNeighbourhood.GeneralIn.exists`).

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.coordPoint`: the `k`-point of `𝔸^{dim V}_k` with given
  coordinates.
* `AlgebraicGeometry.GoodNeighbourhood.GeneralIn`: the property holds for a general member.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.GeneralIn.mono`, `GeneralIn.and`, `GeneralIn.forall_fin`:
  closure properties.
* `AlgebraicGeometry.GoodNeighbourhood.GeneralIn.of_notMem`: avoiding a proper subspace is general.
* `AlgebraicGeometry.GoodNeighbourhood.GeneralIn.exists`: a general property has a witness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

variable (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The `k`-point of the parameter space `𝔸^{dim V}_k` with coordinate tuple `a`. -/
def coordPoint (a : Fin (Module.finrank k V) → k) :
    Spec (.of k) ⟶ 𝔸(ULift.{u} (Fin (Module.finrank k V)); Spec (.of k)) :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    (fun i => (Scheme.ΓSpecIso (.of k)).inv (a i.down))

/-- **A property holds for a general `k`-rational member of `V`**: there are a nonempty open `U`
of `𝔸^{dim V}_k` and finitely many nonzero linear forms `ℓ` on `V` such that `P` holds at
`Σ aⱼ bⱼ` whenever `a` is a `k`-point of `U` and no `ℓ` vanishes there. -/
def GeneralIn (P : V → Prop) : Prop :=
  ∃ U : (𝔸(ULift.{u} (Fin (Module.finrank k V)); Spec (.of k))).Opens, U.1.Nonempty ∧
    ∃ (ι : Type u) (_ : Finite ι) (ℓ : ι → V →ₗ[k] k), (∀ i, ℓ i ≠ 0) ∧
      ∀ a : Fin (Module.finrank k V) → k, (∀ pt, coordPoint k V a pt ∈ U) →
        (∀ i, ℓ i (∑ j, a j • Module.finBasis k V j) ≠ 0) →
          P (∑ j, a j • Module.finBasis k V j)

/-- The family of divisors on `Spec k` with linear system `V`, basis `Module.finBasis k V` and
zero presentation, whose parameter space is `𝔸^{dim V}_k`. -/
def auxFamily : Stacks.Bertini.FamilyDivisors.{u, u} where
  k := k
  V := V
  X := Spec (.of k)
  toBase := 𝟙 _
  L := Stacks.Ample.unitModule (Spec (.of k))
  isInvertible := Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule _
  ψ := 0
  basis := Module.finBasis k V

variable {k V}

/-- The affine space `𝔸^{dim V}_k` over a field `k` is irreducible. -/
theorem irreducibleSpace_affineSpace :
    IrreducibleSpace (𝔸(ULift.{u} (Fin (Module.finrank k V)); Spec (.of k))) :=
  (auxFamily k V).irreducibleSpace_parameterBase

/-- If `P` holds for a general member of `V` and `P` implies `Q`, then `Q` holds for a general
member of `V`. -/
theorem GeneralIn.mono {P Q : V → Prop} (h : GeneralIn k V P) (hPQ : ∀ v, P v → Q v) :
    GeneralIn k V Q := by
  obtain ⟨U, hU, ι, hι, ℓ, hℓ, hP⟩ := h
  exact ⟨U, hU, ι, hι, ℓ, hℓ, fun a ha hℓa => hPQ _ (hP a ha hℓa)⟩

/-- **Two general properties hold together**: if `P` and `Q` each hold for a general member of
`V`, then so does `P ∧ Q`. -/
theorem GeneralIn.and {P Q : V → Prop} (hP : GeneralIn k V P) (hQ : GeneralIn k V Q) :
    GeneralIn k V (fun v => P v ∧ Q v) := by
  obtain ⟨U, hU, ι, hι, ℓ, hℓ, hP⟩ := hP
  obtain ⟨U', hU', ι', hι', ℓ', hℓ', hQ⟩ := hQ
  have := irreducibleSpace_affineSpace (k := k) (V := V)
  have hUU' : (U ⊓ U').1.Nonempty := by
    obtain ⟨y, -, hy⟩ := (IrreducibleSpace.isIrreducible_univ
      (𝔸(ULift.{u} (Fin (Module.finrank k V)); Spec (.of k)))).2 (U : Set _) (U' : Set _)
      U.isOpen U'.isOpen (let ⟨y, hy⟩ := hU; ⟨y, trivial, hy⟩)
      (let ⟨y, hy⟩ := hU'; ⟨y, trivial, hy⟩)
    exact ⟨y, hy⟩
  refine ⟨U ⊓ U', hUU', ι ⊕ ι', inferInstance, Sum.elim ℓ ℓ', ?_, fun a ha hℓa => ⟨?_, ?_⟩⟩
  · rintro (i | i)
    · exact hℓ i
    · exact hℓ' i
  · exact hP a (fun pt => (ha pt).1) (fun i => hℓa (Sum.inl i))
  · exact hQ a (fun pt => (ha pt).2) (fun i => hℓa (Sum.inr i))

/-- The whole parameter space `𝔸^{dim V}_k` is a nonempty open. -/
private theorem nonempty_top_opens :
    (⊤ : (𝔸(ULift.{u} (Fin (Module.finrank k V)); Spec (.of k))).Opens).1.Nonempty := by
  have := irreducibleSpace_affineSpace (k := k) (V := V)
  obtain ⟨y⟩ := (inferInstance : Nonempty (𝔸(ULift.{u} (Fin (Module.finrank k V));
    Spec (.of k))))
  exact ⟨y, trivial⟩

/-- The constant property `True` holds for a general member of `V`. -/
theorem generalIn_true : GeneralIn k V (fun _ => True) := by
  exact ⟨⊤, nonempty_top_opens, PEmpty, inferInstance, PEmpty.elim, fun i => i.elim,
    fun _ _ _ => trivial⟩

/-- **Finitely many general properties hold together.** -/
theorem GeneralIn.forall_fin {m : ℕ} {P : Fin m → V → Prop} (h : ∀ i, GeneralIn k V (P i)) :
    GeneralIn k V (fun v => ∀ i, P i v) := by
  induction m with
  | zero => exact (generalIn_true).mono fun v _ i => i.elim0
  | succ m ih =>
    refine ((ih (P := fun i => P i.castSucc) fun i => h _).and (h (Fin.last m))).mono ?_
    rintro v ⟨h₁, h₂⟩ i
    refine Fin.lastCases ?_ (fun j => h₁ j) i
    exact h₂

/-- **Avoiding a proper subspace is general.** -/
theorem GeneralIn.of_notMem (W : Submodule k V) (hW : W ≠ ⊤) :
    GeneralIn k V (fun v => v ∉ W) := by
  obtain ⟨ℓ, hℓ, hWℓ⟩ := W.exists_le_ker_of_lt_top hW.lt_top
  exact ⟨⊤, nonempty_top_opens, PUnit, inferInstance, fun _ => ℓ, fun _ => hℓ,
    fun a _ hℓa hv => hℓa PUnit.unit (LinearMap.mem_ker.mp (hWℓ hv))⟩

/-- **Over an infinite field a general property has a witness.** -/
theorem GeneralIn.exists [Infinite k] {P : V → Prop} (h : GeneralIn k V P) : ∃ v, P v := by
  obtain ⟨U, hU, ι, hι, ℓ, hℓ, hP⟩ := h
  have : Infinite (auxFamily k V).k := ‹Infinite k›
  obtain ⟨a, ha, hℓa⟩ := (auxFamily k V).exists_parameterPoint_mem_and_ne_zero U hU ℓ hℓ
  exact ⟨_, hP a ha hℓa⟩

end AlgebraicGeometry.GoodNeighbourhood

end
