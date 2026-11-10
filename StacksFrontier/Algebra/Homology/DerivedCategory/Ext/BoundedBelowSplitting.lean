module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums

/-!
# A bounded below complex over a category with no `Ext²` is the sum of its cohomologies

Let `𝒜` be a Grothendieck abelian category with `Ext²_𝒜(B, A) = 0` for all objects `A`, `B`
(for instance modules over a Dedekind domain, such as `ℤ`). Then every object `M` of `D(𝒜)`
whose cohomology vanishes below `b` is isomorphic to a countable direct sum
`⨁_{n ≥ 0} A_n[-(b + n)]` of objects of `𝒜` placed in single degrees.

This extends the bounded case,
`DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero`
([Stacks, Tag 0EWX]), to bounded below objects. For each `i ≥ b` the bounded case, applied to the
truncation `τ_{≤ i}M`, produces a morphism `H^i(τ_{≤ i}M)[-i] ⟶ τ_{≤ i}M ⟶ M` which is an
isomorphism on `H^i`; the sum of these morphisms is an isomorphism on every `H^d`, cohomology
commuting with direct sums in `D(𝒜)`, hence an isomorphism.

## Main results

* `DerivedCategory.exists_hom_singleFunctor_isIso_homologyMap`: for `i ≥ b` a morphism from an
  object placed in degree `i` to `M` which is an isomorphism on `H^i`.
* `DerivedCategory.nonempty_iso_sigma_singleFunctor_of_isGE_of_forall_ext_two_eq_zero`: the
  splitting.

## References

* [Stacks Project, Tag 0EWX](https://stacks.math.columbia.edu/tag/0EWX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' w'' v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- In a biproduct whose summands other than `j` have no cohomology in degree `i`, the inclusion
of the `j`-th summand is an isomorphism on `H^i`. -/
theorem isIso_homologyMap_biproduct_ι {J : Type} [Finite J]
    (X : J → DerivedCategory C) (j : J) (i : ℤ)
    (hX : ∀ k, k ≠ j → IsZero ((homologyFunctor C i).obj (X k))) :
    IsIso ((homologyFunctor C i).map (biproduct.ι X j)) := by
  classical
  have := Fintype.ofFinite J
  refine ⟨⟨(homologyFunctor C i).map (biproduct.π X j), ?_, ?_⟩⟩
  · rw [← Functor.map_comp, biproduct.ι_π_self, CategoryTheory.Functor.map_id]
  · have hsplit : ∑ k, biproduct.π X k ≫ biproduct.ι X k =
        biproduct.π X j ≫ biproduct.ι X j +
          ∑ k ∈ Finset.univ.erase j, biproduct.π X k ≫ biproduct.ι X k := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hzero : (homologyFunctor C i).map
        (∑ k ∈ Finset.univ.erase j, biproduct.π X k ≫ biproduct.ι X k) = 0 := by
      rw [Functor.map_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Functor.map_comp, (hX k (Finset.ne_of_mem_erase hk)).eq_of_tgt
        ((homologyFunctor C i).map (biproduct.π X k)) 0, zero_comp]
    have h := congrArg (homologyFunctor C i).map (biproduct.total.symm.trans hsplit)
    rw [CategoryTheory.Functor.map_id, Functor.map_add, hzero, add_zero, Functor.map_comp] at h
    exact h.symm

/-- An object placed in degree `j ≠ i` has no cohomology in degree `i`. -/
private theorem isZero_homologyFunctor_obj_singleFunctor_obj_aux (A : C) {i j : ℤ}
    (hij : j ≠ i) : IsZero ((homologyFunctor C i).obj ((singleFunctor C j).obj A)) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact isZero_of_isLE _ j i hlt
  · exact isZero_of_isGE _ j i hgt

variable [HasExt.{w''} C]

/-- **A morphism from one degree, an isomorphism on cohomology there.** Let `Ext²_𝒜` vanish and
let `M` have no cohomology below `b`. For `i ≥ b` there is a morphism from `H^i(τ_{≤ i}M)` placed
in degree `i` to `M` which is an isomorphism on `H^i`. -/
theorem exists_hom_singleFunctor_isIso_homologyMap
    (h : ∀ (A B : C) (e : Abelian.Ext.{w''} B A 2), e = 0) (M : DerivedCategory C) (b i : ℤ)
    (hbi : b ≤ i) [M.IsGE b] :
    ∃ c : (singleFunctor C i).obj ((homologyFunctor C i).obj
        ((TStructure.t.truncLE i).obj M)) ⟶ M,
      IsIso ((homologyFunctor C i).map c) := by
  classical
  let K := (TStructure.t.truncLE i).obj M
  obtain ⟨e⟩ := nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero
    K b i h
  let X := fun k : Finset.Icc b i => (singleFunctor C k.1).obj ((homologyFunctor C k.1).obj K)
  let j : Finset.Icc b i := ⟨i, Finset.mem_Icc.mpr ⟨hbi, le_rfl⟩⟩
  refine ⟨biproduct.ι X j ≫ e.inv ≫ (TStructure.t.truncLEι i).app M, ?_⟩
  have h₁ : IsIso ((homologyFunctor C i).map (biproduct.ι X j)) :=
    isIso_homologyMap_biproduct_ι X j i fun k hk =>
      isZero_homologyFunctor_obj_singleFunctor_obj_aux _ fun hki => hk (Subtype.ext hki)
  have h₃ : IsIso ((homologyFunctor C i).map ((TStructure.t.truncLEι i).app M)) :=
    Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app i i le_rfl M
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

omit [HasExt C] in
/-- In a degree in which an object placed in degree `j ≠ i` has no cohomology. -/
theorem isZero_homologyFunctor_obj_singleFunctor_obj (A : C) {i j : ℤ} (hij : j ≠ i) :
    IsZero ((homologyFunctor C i).obj ((singleFunctor C j).obj A)) :=
  isZero_homologyFunctor_obj_singleFunctor_obj_aux A hij

variable [IsGrothendieckAbelian.{w} C]

attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

/-- **A bounded below object over a category with no `Ext²` is the sum of its cohomologies.** Let
`𝒜` be a Grothendieck abelian category with `Ext²_𝒜(B, A) = 0` for all objects `A`, `B`, and let
`M ∈ D(𝒜)` have no cohomology below `b`. Then `M` is isomorphic to a countable direct sum
`⨁_{n ≥ 0} A_n[-(b + n)]` of objects of `𝒜` placed in single degrees. -/
theorem nonempty_iso_sigma_singleFunctor_of_isGE_of_forall_ext_two_eq_zero
    (h : ∀ (A B : C) (e : Abelian.Ext.{w''} B A 2), e = 0) (M : DerivedCategory C) (b : ℤ)
    [M.IsGE b] :
    ∃ A : ULift.{w} ℕ → C,
      Nonempty ((∐ fun n : ULift.{w} ℕ => (singleFunctor C (b + n.down)).obj (A n)) ≅ M) := by
  choose c hc using fun n : ULift.{w} ℕ =>
    exists_hom_singleFunctor_isIso_homologyMap h M b (b + n.down) (by omega)
  let A := fun n : ULift.{w} ℕ => (homologyFunctor C (b + n.down)).obj
    ((TStructure.t.truncLE (b + n.down)).obj M)
  let X := fun n : ULift.{w} ℕ => (singleFunctor C (b + n.down)).obj (A n)
  suffices hiso : IsIso (Sigma.desc c : ∐ X ⟶ M) from ⟨A, ⟨asIso (Sigma.desc c : ∐ X ⟶ M)⟩⟩
  rw [isIso_iff]
  intro d
  have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor C (J := ULift.{w} ℕ) d
  have hcol := isColimitOfPreserves (homologyFunctor C d) (colimit.isColimit (Discrete.functor X))
  rcases lt_or_ge d b with hdb | hdb
  · have hs : IsZero ((homologyFunctor C d).obj (∐ X)) := by
      rw [IsZero.iff_id_eq_zero]
      refine hcol.hom_ext fun n => ?_
      exact (isZero_homologyFunctor_obj_singleFunctor_obj _ (by omega)).eq_of_src _ _
    exact ⟨⟨0, hs.eq_of_src _ _, (isZero_of_isGE M b d hdb).eq_of_src _ _⟩⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = b + m := ⟨(d - b).toNat, by omega⟩
    let n₀ : ULift.{w} ℕ := ⟨m⟩
    have hc₀ : IsIso ((homologyFunctor C (b + m)).map (c n₀)) := hc n₀
    refine ⟨⟨inv ((homologyFunctor C (b + m)).map (c n₀)) ≫
      (homologyFunctor C (b + m)).map (Sigma.ι X n₀), ?_, ?_⟩⟩
    · refine hcol.hom_ext fun n => ?_
      dsimp
      rw [Category.comp_id, ← Functor.map_comp_assoc, Sigma.ι_comp_desc]
      by_cases hn : n.as = n₀
      · obtain ⟨n⟩ := n
        dsimp at hn
        subst hn
        simp
      · have hn' : b + n.as.down ≠ b + m := fun h' =>
          hn (ULift.ext (show n.as.down = m by omega))
        exact (isZero_homologyFunctor_obj_singleFunctor_obj _ hn').eq_of_src _ _
    · rw [Category.assoc, ← Functor.map_comp, Sigma.ι_comp_desc, IsIso.inv_hom_id]

end DerivedCategory
