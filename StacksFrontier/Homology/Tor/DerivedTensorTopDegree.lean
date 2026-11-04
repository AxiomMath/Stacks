module

public import StacksFrontier.Homology.Tor.DerivedTensorDegreeZero
public import StacksFrontier.Homology.Tor.DerivedTensorProductIsLE
public import StacksFrontier.Homology.Tor.ResidueLengthTop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top cohomology of a derived tensor product with a module

Let `A` be a commutative ring, `X` an object of `D(A)` with no cohomology above degree `p`, and
`N` an `A`-module. Then `H^p(X ⊗ᴸ_A N[0]) ≅ H^p(X) ⊗_A N`; `X` is not assumed bounded below.

Combined with the global form of Nakayama's lemma (a finite `A`-module `M` with `M ⊗_A A/m = 0` at
every maximal ideal `m` vanishes), this shows that if the cohomology modules of `X` are finite and
`X ⊗ᴸ_A (A/m)[0]` has no cohomology above degree zero for every maximal ideal `m`, then `X` has no
cohomology above degree zero.

## Main results

* `StacksDraft.Nakayama.subsingleton_of_forall_subsingleton_tensor_quotient`: a finite module whose
  tensor products with all residue fields `A / m` vanish is zero.
* `Stacks.DerivedTensor.nonempty_homology_top_derivedTensor_single_iso`: for `X` in `D^{≤ p}`,
  `H^p(X ⊗ᴸ_A N[0]) ≅ H^p(X) ⊗_A N`.
* `Stacks.DerivedTensor.isLE_zero_of_forall_isLE_zero_derivedTensor_quotient`: an object bounded
  above with finite cohomology modules, all of whose derived fibres `X ⊗ᴸ_A (A/m)[0]` lie in
  `D^{≤ 0}`, lies in `D^{≤ 0}`.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Nakayama

universe u

/-- A finite module over a commutative ring whose tensor product with every residue field `A / m`
vanishes is itself zero. -/
@[ega "0 7.1.13" "more general", ega "IV 2.5.5.4" "more general"]
theorem subsingleton_of_forall_subsingleton_tensor_quotient {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (h : ∀ m : Ideal A, m.IsMaximal → Subsingleton (TensorProduct A M (A ⧸ m))) :
    Subsingleton M := by
  by_contra hns
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Module.annihilator A M)
    fun he ↦ hns (Module.annihilator_eq_top_iff.mp he)
  have htop : (m • (⊤ : Submodule A M)) = ⊤ := Submodule.Quotient.subsingleton_iff.mp
    ((TensorProduct.tensorQuotEquivQuotSMul M m).toEquiv.subsingleton_congr.mp (h m hm))
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m ⊤ Module.Finite.fg_top htop.ge
  have hone : (1 : A) ∈ m := by
    simpa using sub_mem (hle (Module.mem_annihilator.mpr fun x ↦ hr2 x Submodule.mem_top)) hr1
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hone isUnit_one)

end StacksDraft.Nakayama

namespace Stacks.DerivedTensor

open CochainComplex.DerivedTensor

universe u

variable (A : Type u) [CommRing A]

/-- For `X` in `D^{≤ p}(A)` and an `A`-module `N`, `H^p(X ⊗ᴸ_A N[0]) ≅ H^p(X) ⊗_A N`; `X` is not
assumed bounded below. -/
theorem nonempty_homology_top_derivedTensor_single_iso
    (X : DObj A) (p : ℤ) (hX : X.IsLE p) (N : ModuleCat.{u} A) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        (((canonicalDerivedTensorProductFunctor A).obj X).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) ≅
      ModuleCat.of A (TensorProduct A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj X) N)) := by
  set S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N with hS
  set F := (canonicalDerivedTensorProduct A).tensor.flip.obj S
  have hway : ∀ (Y : DObj A) (n : ℤ), Y.IsLE n → (F.obj Y).IsLE (n + 0) := by
    intro Y n hY
    have : S.IsLE 0 := by rw [hS]; infer_instance
    exact isLE_tensor (canonicalDerivedTensorProduct A) Y S n 0
  have hsingle : ∀ i : ℤ, i < p → (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X))).IsLE 0 := fun i _ ↦ by
    simpa using hway ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) 0 inferInstance
  exact (StacksDraft.ResidueLength.nonempty_homology_iso_homology_map_single_top_of_isLE_homology
    F X p 0 hX hway hsingle).map (· ≪≫ homologyZeroIsoTensorProduct A _ N)

/-- Let `P` be an object of `D(A)` bounded above with finite cohomology modules. If
`P ⊗ᴸ_A (A/m)[0]` lies in `D^{≤ 0}` for every maximal ideal `m`, then `P` lies in `D^{≤ 0}`. -/
theorem isLE_zero_of_forall_isLE_zero_derivedTensor_quotient
    (P : DObj A) (p : ℤ) (hP : P.IsLE p)
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (h : ∀ m : Ideal A, m.IsMaximal →
      (((canonicalDerivedTensorProductFunctor A).obj P).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ m)))).IsLE 0) :
    P.IsLE 0 := by
  have vanish : ∀ n : ℤ, 0 < n → P.IsLE n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj P) := by
    intro n hn hPn
    rw [ModuleCat.isZero_iff_subsingleton]
    refine StacksDraft.Nakayama.subsingleton_of_forall_subsingleton_tensor_quotient
      (A := A) _ fun m hm ↦ ?_
    obtain ⟨e⟩ := nonempty_homology_top_derivedTensor_single_iso A P n hPn
      (ModuleCat.of A (A ⧸ m))
    exact ModuleCat.isZero_iff_subsingleton.mp
      (((DerivedCategory.isLE_iff _ 0).1 (h m hm) n hn).of_iso e.symm)
  have key : ∀ k : ℕ, P.IsLE (k : ℤ) → P.IsLE 0 := by
    intro k
    induction k with
    | zero => exact fun h0 ↦ by simpa using h0
    | succ j ih =>
        intro hj
        refine ih ((DerivedCategory.isLE_iff P (j : ℤ)).2 fun i hi ↦ ?_)
        have hj' : P.IsLE ((j : ℤ) + 1) := by simpa using hj
        obtain rfl | hlt := (show (j : ℤ) + 1 ≤ i by lia).eq_or_lt
        · exact vanish _ (by lia) hj'
        · exact (DerivedCategory.isLE_iff P ((j : ℤ) + 1)).1 hj' i hlt
  exact key p.toNat
    (DerivedCategory.TStructure.t.isLE_of_le _ p (p.toNat : ℤ) (Int.self_le_toNat p))

end Stacks.DerivedTensor

end
