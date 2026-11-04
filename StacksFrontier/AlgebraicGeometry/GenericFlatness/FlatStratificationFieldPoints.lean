module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.NoetherianFlatStratification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Field-valued points of a flat stratification

Let `f : X ⟶ S` be a morphism of finite type to a Noetherian scheme. By the Noetherian case of
Stacks 0H3Z (`AlgebraicGeometry.HasFlatStratification.of_isNoetherian`) the base `S` is covered by
finitely many locally closed subschemes, the strata `S_i ∖ S_{i+1}`, over each of which the base
change of `f` is flat. This file records the two facts a boundedness argument needs about them:
every stratum is a Noetherian scheme immersed in `S`, and every field-valued point of `S` factors
through one of the strata.

## Main results

* `AlgebraicGeometry.exists_flat_strata_of_isNoetherian`: finitely many Noetherian schemes `Tᵢ`
  with immersions `jᵢ : Tᵢ ⟶ S` over which `f` becomes flat, through one of which every morphism
  from the spectrum of a field to `S` factors.

## Implementation notes

The stratum through which a field-valued point `s : Spec K ⟶ S` factors is found from the least
index `j` of the chain of ideal sheaves whose support misses the image point of `s`: the index is
positive because the first closed subscheme is a thickening, and the point lies in the support of
the previous ideal sheaf by minimality. Factoring `s` through a closed subscheme whose support
contains its image is the statement that the base change of the closed immersion to `Spec K` is a
surjective closed immersion into a reduced scheme, hence an isomorphism (Mathlib's
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`).

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A morphism from the spectrum of a field factors through a closed subscheme containing its
image.** The base change of the closed immersion to `Spec K` is a closed immersion with nonempty,
hence full, image into a reduced one-point scheme, so it is an isomorphism. -/
@[ega "I 5.2.2" "special case"]
theorem exists_lift_subschemeι_of_mem_support {S : Scheme.{u}} (I : S.IdealSheafData)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ S) (x : Spec (.of K))
    (hx : s.base x ∈ I.support) :
    ∃ s' : Spec (.of K) ⟶ I.subscheme, s' ≫ I.subschemeι = s := by
  have hsurj : Surjective (pullback.snd I.subschemeι s) := by
    refine ⟨fun y => ?_⟩
    have hy : y = x := Subsingleton.elim _ _
    subst hy
    have hx' : s.base y ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hx
    obtain ⟨z, hz⟩ := hx'
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
    exact ⟨w, hw⟩
  have := hsurj
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd I.subschemeι s)
  refine ⟨inv (pullback.snd I.subschemeι s) ≫ pullback.fst I.subschemeι s, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- **The strata of a flat stratification over a Noetherian base, with their field-valued
points.** Let `f : X ⟶ S` be of finite type and quasi-compact with `S` Noetherian. There are
finitely many Noetherian schemes `Tᵢ` with immersions `jᵢ : Tᵢ ⟶ S` such that each base change
`X ×_S Tᵢ ⟶ Tᵢ` is flat and every morphism from the spectrum of a field to `S` factors through
one of the `jᵢ`. -/
theorem exists_flat_strata_of_isNoetherian {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (t : ℕ) (T : Fin t → Scheme.{u}) (j : ∀ i, T i ⟶ S),
      (∀ i, IsImmersion (j i)) ∧ (∀ i, IsNoetherian (T i)) ∧
      (∀ i, Flat (pullback.snd f (j i))) ∧
      ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
        ∃ i, ∃ s' : Spec (.of K) ⟶ T i, s' ≫ j i = s := by
  obtain ⟨t, I, hthick, -, -, hlast, hflat⟩ := HasFlatStratification.of_isNoetherian f
  let Z : Fin t → S.IdealSheafData := fun i => I i.castSucc
  let U : ∀ i, (Z i).subscheme.Opens := fun i =>
    (Z i).subschemeι ⁻¹ᵁ (I i.succ).support.compl
  refine ⟨t, fun i => (U i).toScheme, fun i => (U i).ι ≫ (Z i).subschemeι,
    fun i => inferInstance, fun i => ?_, hflat, ?_⟩
  · have hemb : Topology.IsEmbedding ((U i).ι ≫ (Z i).subschemeι).base :=
      ((U i).ι ≫ (Z i).subschemeι).isEmbedding
    exact { toIsLocallyNoetherian :=
              LocallyOfFiniteType.isLocallyNoetherian ((U i).ι ≫ (Z i).subschemeι)
            toCompactSpace := ⟨hemb.isCompact_iff.mpr (NoetherianSpace.isCompact _)⟩ }
  intro K _ s
  let x : Spec (.of K) := Classical.arbitrary _
  have hex : ∃ k : ℕ, ∃ hk : k < t + 1, s.base x ∉ (I ⟨k, hk⟩).support :=
    ⟨t, Nat.lt_succ_self t, by
      have : (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1)) = Fin.last t := rfl
      rw [this, hlast, Scheme.IdealSheafData.support_top]
      exact fun h => h⟩
  classical
  let k := Nat.find hex
  obtain ⟨hk, hxk⟩ := Nat.find_spec hex
  have hmin : ∀ l < k, ∀ hl : l < t + 1, s.base x ∈ (I ⟨l, hl⟩).support := fun l hl hl' => by
    by_contra h
    exact Nat.find_min hex hl ⟨hl', h⟩
  have hk0 : k ≠ 0 := by
    intro h0
    have hsupp : (I 0).support = ⊤ :=
      (Scheme.IdealSheafData.isThickening_subschemeι_iff (I 0)).mp hthick
    apply hxk
    have : (⟨k, hk⟩ : Fin (t + 1)) = 0 := Fin.ext h0
    rw [this, hsupp]
    trivial
  obtain ⟨i, hi⟩ : ∃ i : ℕ, k = i + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hit : i < t := by omega
  let i' : Fin t := ⟨i, hit⟩
  have hxi : s.base x ∈ (Z i').support := hmin i (by omega) (by omega)
  have hxi' : s.base x ∉ (I i'.succ).support := by
    have : i'.succ = (⟨k, hk⟩ : Fin (t + 1)) := Fin.ext (by simp [i', hi])
    rw [this]
    exact hxk
  obtain ⟨s₁, hs₁⟩ := exists_lift_subschemeι_of_mem_support (Z i') K s x hxi
  have hrange : Set.range s₁.base ⊆ ((U i' : (Z i').subscheme.Opens) : Set (Z i').subscheme) := by
    rintro _ ⟨y, rfl⟩
    have hy : y = x := Subsingleton.elim _ _
    subst hy
    show ((Z i').subschemeι.base (s₁.base x)) ∈ ((I i'.succ).support.compl : Set S)
    have h2 : (Z i').subschemeι.base (s₁.base x) = s.base x := by
      rw [← Scheme.Hom.comp_apply, hs₁]
    rw [h2]
    exact hxi'
  refine ⟨i', IsOpenImmersion.lift (U i').ι s₁ (by rwa [Scheme.Opens.range_ι]), ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hs₁]

end AlgebraicGeometry

end
