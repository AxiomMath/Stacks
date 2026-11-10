module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Data.Int.Interval

/-!
# Homogeneous bases of graded vector spaces

Three facts of linear algebra on `ℤ`-graded vector spaces `⨁_j M_j`, consumed by the comparison
of de Rham cohomology with its base change to an extension of the base field
([Stacks, Tag 0FM0] read on cohomology over a field).

* A graded vector space with finite-dimensional pieces, vanishing outside an interval, has a
  finite basis of homogeneous vectors (`exists_basis_lof`).
* The vectors of degree `m` of a homogeneous basis form a basis of `M_m`
  (`exists_basis_component`).
* Conversely to the basis criterion
  `Stacks.Cohomology.OnePointDetection.isIso_biproduct_desc_of_basis`: if
  `⨁ d_i : ⨁ P_i ⟶ E` is an isomorphism and the total cohomology of each `P_i` is the line
  through a nonzero class `g_i` in degree `n_i`, then the classes `d_i(g_i)` form a basis of the
  total cohomology of `E` (`exists_basis_of_isIso_biproduct_desc`).

## Main results

* `Stacks.WeilDeRham.exists_basis_lof`
* `Stacks.WeilDeRham.exists_basis_component`
* `Stacks.WeilDeRham.exists_basis_of_isIso_biproduct_desc`

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.WeilDeRham

/-! ### Homogeneous bases -/

section Graded

variable {R : Type u} [Field R] (M : ℤ → Type u) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

/-- **A finite homogeneous basis.** If every `M_j` is finite-dimensional and `M_j = 0` outside
`[a, b]`, then `⨁_j M_j` has a basis indexed by `Fin N` whose `i`-th vector is a vector of
`M_{n_i}`. -/
theorem exists_basis_lof [∀ j, FiniteDimensional R (M j)] (a b : ℤ)
    (hz : ∀ j, j < a ∨ b < j → Subsingleton (M j)) :
    ∃ (N : ℕ) (n : Fin N → ℤ) (v : ∀ i, M (n i)) (B : Module.Basis (Fin N) R (DirectSum ℤ M)),
      ∀ i, B i = DirectSum.lof R ℤ M (n i) (v i) := by
  classical
  let J := Σ j : Set.Icc a b, Fin (Module.finrank R (M j))
  let F : J → DirectSum ℤ M := fun t =>
    DirectSum.lof R ℤ M t.1.1 (Module.finBasis R (M t.1.1) t.2)
  have hli : LinearIndependent R F := by
    have h := DFinsupp.linearIndependent_single (R := R) (M := M)
      (fun j => Module.finBasis R (M j)) (fun j => (Module.finBasis R (M j)).linearIndependent)
    refine h.comp (fun t : J => (⟨t.1.1, t.2⟩ : Σ j : ℤ, Fin (Module.finrank R (M j)))) ?_
    rintro ⟨⟨j, hj⟩, s⟩ ⟨⟨j', hj'⟩, s'⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h
    subst h
    rfl
  have hsp : ∀ x : DirectSum ℤ M, x ∈ Submodule.span R (Set.range F) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | of j y =>
      by_cases hj : j ∈ Set.Icc a b
      · rw [← DirectSum.lof_eq_of R, ← (Module.finBasis R (M j)).sum_repr y, map_sum]
        refine Submodule.sum_mem _ fun s _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨j, hj⟩, s⟩, rfl⟩)
      · have : Subsingleton (M j) := hz j (by
          simp only [Set.mem_Icc, not_and_or, not_le] at hj
          exact hj)
        rw [Subsingleton.elim y 0, map_zero]
        exact Submodule.zero_mem _
  let B₀ := Module.Basis.mk hli fun x _ => hsp x
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => (e.symm i).1.1,
    fun i => Module.finBasis R (M (e.symm i).1.1) (e.symm i).2, B₀.reindex e, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]

/-- **The vectors of degree `m` of a homogeneous basis form a basis of `M_m`.** If the `i`-th
vector of a basis of `⨁_j M_j` lies in `M_{n_i}`, then the `m`-th components of the vectors with
`n_i = m` form a basis of `M_m`. -/
theorem exists_basis_component {ι : Type*} [Finite ι] (b : Module.Basis ι R (DirectSum ℤ M))
    (n : ι → ℤ) (v : ∀ i, M (n i)) (hb : ∀ i, b i = DirectSum.lof R ℤ M (n i) (v i)) (m : ℤ) :
    ∃ b' : Module.Basis {i // n i = m} R (M m),
      ∀ t, b' t = DirectSum.component R ℤ M m (DirectSum.lof R ℤ M (n t) (v t)) := by
  classical
  have := Fintype.ofFinite ι
  have aux : ∀ (j : ℤ) (x : M j), j = m →
      DirectSum.lof R ℤ M m (DirectSum.component R ℤ M m (DirectSum.lof R ℤ M j x)) =
        DirectSum.lof R ℤ M j x := by
    rintro j x rfl
    rw [DirectSum.component.lof_self]
  have hhom : ∀ t : {i // n i = m},
      DirectSum.lof R ℤ M m (DirectSum.component R ℤ M m (b t)) = b t := by
    rintro ⟨i, hi⟩
    rw [hb i]
    exact aux (n i) (v i) hi
  have hli : LinearIndependent R fun t : {i // n i = m} => DirectSum.component R ℤ M m (b t) := by
    have h : LinearIndependent R fun t : {i // n i = m} => b t :=
      b.linearIndependent.comp _ Subtype.val_injective
    refine LinearIndependent.of_comp (DirectSum.lof R ℤ M m) ?_
    convert h using 1
    funext t
    exact hhom t
  have hsp : ∀ y : M m, y ∈ Submodule.span R
      (Set.range fun t : {i // n i = m} => DirectSum.component R ℤ M m (b t)) := by
    intro y
    have hy := congrArg (DirectSum.component R ℤ M m) (b.sum_repr (DirectSum.lof R ℤ M m y))
    rw [DirectSum.component.lof_self, map_sum] at hy
    rw [← hy]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    by_cases hi : n i = m
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · have h0 : DirectSum.component R ℤ M m (b i) = 0 := by
        rw [hb i, DirectSum.component.of, dite_eq_right hi]
      rw [h0, smul_zero]
      exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli fun y _ => hsp y, fun t => (Module.Basis.mk_apply _ _ _).trans
    (congrArg _ (hb t))⟩

end Graded

/-! ### Bases from isomorphisms out of sums of lines -/

section Iso

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
  {R : Type u} [Field R] (H : ℤ → C ⥤ ModuleCat.{u} R) [∀ k, (H k).Additive]

/-- **The images of the generators under an isomorphism out of a sum of lines form a basis.** Let
`H^k`, `k ∈ ℤ`, be additive functors to `R`-vector spaces and let `d_i : P_i ⟶ E` be morphisms such
that the total cohomology `⨁_k H^k(P_i)` is spanned by a class `g_i` in degree `n_i`, and is
nonzero. If
`⨁ d_i : ⨁ P_i ⟶ E` is an isomorphism, then the classes `d_i(g_i)` form a basis of
`⨁_k H^k(E)`. -/
theorem exists_basis_of_isIso_biproduct_desc {N : ℕ} (n : Fin N → ℤ) (P : Fin N → C) (E : C)
    (d : ∀ i, P i ⟶ E) (g : ∀ i, (H (n i)).obj (P i)) (hnt : ∀ i, Nontrivial ((H (n i)).obj (P i)))
    (hspan : ∀ (i : Fin N) (j : ℤ) (x : (H j).obj (P i)),
      ∃ c : R, DirectSum.lof R ℤ (fun k => (H k).obj (P i)) j x =
        c • DirectSum.lof R ℤ (fun k => (H k).obj (P i)) (n i) (g i))
    (hd : IsIso (biproduct.desc d)) :
    ∃ b : Module.Basis (Fin N) R (DirectSum ℤ fun k => (H k).obj E),
      ∀ i, b i = DirectSum.lof R ℤ (fun k => (H k).obj E) (n i)
        (((H (n i)).map (d i)).hom (g i)) := by
  classical
  have hg : ∀ i, g i ≠ 0 := by
    intro i h0
    obtain ⟨x, hx⟩ := exists_ne (0 : (H (n i)).obj (P i))
    obtain ⟨c, hc⟩ := hspan i (n i) x
    rw [h0, map_zero, smul_zero] at hc
    exact hx (DirectSum.of_injective (n i) (hc.trans (map_zero _).symm))
  let TP : ℤ → Type u := fun k => (H k).obj (⨁ P)
  let e : Fin N → DirectSum ℤ TP := fun i =>
    DirectSum.lof R ℤ TP (n i) (((H (n i)).map (biproduct.ι P i)).hom (g i))
  -- the generators span
  have hspanP : ∀ x : DirectSum ℤ TP, x ∈ Submodule.span R (Set.range e) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | of k y =>
      have hy : y = ∑ i, ((H k).map (biproduct.ι P i)).hom
          (((H k).map (biproduct.π P i)).hom y) := by
        have h := congrArg (fun z => ((H k).map z).hom y) (biproduct.total (f := P))
        simp only [CategoryTheory.Functor.map_id, (H k).map_sum,
          ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id, LinearMap.id_apply,
          Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [← DirectSum.lof_eq_of R, hy, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := hspan i k (((H k).map (biproduct.π P i)).hom y)
      have := congrArg (DirectSum.lmap fun k => ((H k).map (biproduct.ι P i)).hom) hc
      rw [DirectSum.lmap_lof, map_smul, DirectSum.lmap_lof] at this
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  -- the generators are linearly independent
  have hli : LinearIndependent R e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h2 : ∀ i, (DirectSum.lmap fun k => ((H k).map (biproduct.π P j)).hom) (c i • e i) =
        if i = j then c j • DirectSum.lof R ℤ (fun k => (H k).obj (P j)) (n j) (g j) else 0 := by
      intro i
      rw [map_smul, DirectSum.lmap_lof]
      split_ifs with hij
      · subst hij
        have hid : ((H (n i)).map (biproduct.π P i)).hom
            (((H (n i)).map (biproduct.ι P i)).hom (g i)) = g i := by
          change ((H (n i)).map (biproduct.ι P i) ≫ (H (n i)).map (biproduct.π P i)).hom (g i) = _
          rw [← Functor.map_comp, biproduct.ι_π_self, CategoryTheory.Functor.map_id]
          rfl
        rw [hid]
      · have h0 : ((H (n i)).map (biproduct.π P j)).hom
            (((H (n i)).map (biproduct.ι P i)).hom (g i)) = 0 := by
          change ((H (n i)).map (biproduct.ι P i) ≫ (H (n i)).map (biproduct.π P j)).hom (g i) = _
          rw [← Functor.map_comp, biproduct.ι_π_ne _ hij, Functor.map_zero]
          rfl
        rw [h0, map_zero, smul_zero]
    have h1 := congrArg (DirectSum.lmap fun k => ((H k).map (biproduct.π P j)).hom) hc
    rw [map_sum, map_zero] at h1
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd (DirectSum.of_injective (n j) (h.trans (map_zero _).symm)) (hg j)
  -- the isomorphism on total cohomology
  have := hd
  let φ : ∀ k, TP k →ₗ[R] (H k).obj E := fun k => ((H k).map (biproduct.desc d)).hom
  have hbij : ∀ k, Function.Bijective (φ k) := fun k =>
    (ConcreteCategory.isIso_iff_bijective ((H k).map (biproduct.desc d))).1 inferInstance
  let Φ := LinearEquiv.ofBijective (DirectSum.lmap φ)
    ⟨(DirectSum.lmap_injective φ).2 fun k => (hbij k).1,
      (DirectSum.lmap_surjective φ).2 fun k => (hbij k).2⟩
  refine ⟨(Module.Basis.mk hli fun x _ => hspanP x).map Φ, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  change DirectSum.lmap φ (e i) = _
  rw [DirectSum.lmap_lof]
  congr 1
  change ((H (n i)).map (biproduct.ι P i) ≫ (H (n i)).map (biproduct.desc d)).hom (g i) = _
  rw [← Functor.map_comp, biproduct.ι_desc]

end Iso

end Stacks.WeilDeRham

end
