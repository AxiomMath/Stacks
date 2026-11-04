module

public import StacksCore.Algebra.Algebra.Subalgebra.DivisionRing
public import StacksCore.Algebra.Central.Matrix
public import StacksCore.Algebra.Split.Finrank

/-!
# Every Brauer class has a finite separable splitting field

This is the "in particular" half of Stacks tag 0752. The subfield half — a finite-dimensional
central division algebra contains a separable maximal subfield (Koethe's theorem) — is
`DivisionRing.exists_separable_maxSubfield`, in
`StacksCore.Algebra.Algebra.Subalgebra.DivisionRing`.

The passage from one to the other is the Brauer-class argument the tag sketches: a central
simple `A` is `Matrix (Fin n) (Fin n) D` for a central division algebra `D` by
Wedderburn–Artin, a separable maximal subfield `L ⊆ D` splits `D` because maximal subfields of
a division algebra are exactly the ones of the maximal degree
(`DivisionRing.split_iff_finrank` together with `Subalgebra.isMaximal_comm_iff_finrank`), and
splitting is a class invariant (`Algebra.isSplit_congr`). Finally `L` is transported into the
chosen algebraic closure along `IsAlgClosed.lift`, so the statement can quantify over
`IntermediateField k k_bar` rather than over abstract extensions.

`exists_finite_galois_split` upgrades separable to Galois by passing to the normal closure,
which is the form Stacks tag 0753 (5) asks for.
-/

@[expose] public section

open scoped IsMulCommutative

section MaximalSubfield

variable {k D : Type*} [Field k] [DivisionRing D] [Algebra k D] [Module.Finite k D]
  [Algebra.IsCentral k D]

/-- **Stacks 0750**: a maximal subfield of a finite central division algebra `D` over `k` is a
splitting field for `D`.

"Maximal subfield" is rendered as a subalgebra maximal among the *commutative* subalgebras.
That is the same notion here: every subalgebra of a finite-dimensional division algebra is a
division ring, and every commutative one is a field (`Subalgebra.fieldOfIsMulCommutative`), so
the commutative subalgebras of `D` are exactly its subfields.

Maximality is stated with `Maximal` rather than through the numerical criterion
`Subalgebra.isMaximal_comm_iff_finrank`; the latter is 074V/074W content, and using it here
would make the statement circular with its own proof. -/
@[stacks 0750]
theorem DivisionRing.isSplit_of_maximal_comm (L : Subalgebra k D) [IsMulCommutative L]
    (hL : Maximal (fun S : Subalgebra k D ↦ IsMulCommutative S) L) :
    Algebra.IsSplit k D L := by
  let : Field ↥L := L.fieldOfIsMulCommutative
  rw [DivisionRing.split_iff_finrank L.val, ← Subalgebra.isMaximal_comm_iff_finrank]
  exact (Subalgebra.maximal_comm_iff_self_centralizer L).1 hL

/-- Self-centralizing form of **Stacks 0750**. This is the shape Koethe's theorem
`DivisionRing.exists_separable_maxSubfield` produces, so it is the one downstream callers
want; `Subalgebra.maximal_comm_iff_self_centralizer` identifies it with maximality. -/
theorem DivisionRing.isSplit_of_centralizer_eq (L : Subalgebra k D) [IsMulCommutative L]
    (hL : Subalgebra.centralizer k (L : Set D) = L) :
    Algebra.IsSplit k D L :=
  DivisionRing.isSplit_of_maximal_comm L
    ((Subalgebra.maximal_comm_iff_self_centralizer L).2 hL)

end MaximalSubfield

variable {k A k_bar : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A] [IsSimpleRing A]
  [Algebra.IsCentral k A] [Field k_bar] [Algebra k k_bar] [IsAlgClosed k_bar]

/-- **Stacks 0752**, the "in particular" clause: every Brauer class has a finite separable
splitting field. Concretely, every finite central simple `k`-algebra is split by a finite
separable subextension of any chosen algebraic closure. -/
@[stacks 0752 "in particular: every Brauer class has a finite separable splitting field"]
theorem Algebra.IsCentralSimple.exists_finite_sep_split :
    ∃ K : IntermediateField k k_bar, Module.Finite k K ∧
      Algebra.IsSeparable k K ∧ Algebra.IsSplit k A K := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  have : Algebra.IsCentral k D := .of_matrix (h := .of_algEquiv k _ _ e)
  obtain ⟨L, hL1, hL2⟩ := DivisionRing.exists_separable_maxSubfield (k := k) (D := D)
  have : IsMulCommutative L := (Subalgebra.le_centralizer_iff_isMulCommutative L).1 hL1.ge
  let : Field L := L.fieldOfIsMulCommutative
  have hL3 : IsSplit k A L := by
    rw [isSplit_congr k A D L (by
      rw [BrauerGroup.mk_congr e, BrauerGroup.mk_eq_mk]
      exact ⟨1, n, one_ne_zero, hn.out, ⟨by convert Matrix.uniqueAlgEquiv (m := Fin 1); rfl⟩⟩)]
    exact DivisionRing.isSplit_of_centralizer_eq L hL1
  let e : L ≃ₐ[k] (IsAlgClosed.lift (M := k_bar) (R := k) (S := L)).fieldRange :=
    AlgEquiv.ofInjectiveField _
  exact ⟨_, Module.Finite.of_injective _ e.symm.toLinearEquiv.injective,
    AlgEquiv.Algebra.isSeparable e, IsSplit.of_algEquiv' _ _ hL3 e⟩

/-- Every central simple algebra over a field has a finite Galois splitting field. -/
theorem Algebra.IsCentralSimple.exists_finite_galois_split [Algebra.IsAlgebraic k k_bar] :
    ∃ K : IntermediateField k k_bar, Module.Finite k K ∧ IsGalois k K ∧ Algebra.IsSplit k A K := by
  obtain ⟨K, _, _, hK⟩ := exists_finite_sep_split (k := k) (A := A) (k_bar := k_bar)
  have hk : IsAlgClosure k k_bar := ⟨inferInstance, inferInstance⟩
  set N := IntermediateField.normalClosure k K k_bar with N_def
  use N, inferInstance, ?_
  · exact IsSplit.of_isScalarTower N hK
  have : ∀ f : K →ₐ[k] k_bar, Algebra.IsSeparable k f.fieldRange := fun f ↦
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjective f f.toRingHom.injective)
  exact IsGalois.mk (to_isSeparable := IntermediateField.isSeparable_iSup k k_bar)
