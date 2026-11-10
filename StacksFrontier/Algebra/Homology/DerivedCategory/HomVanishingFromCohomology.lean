module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Homology.Tor.ExtremalDegrees
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Morphisms out of a bounded object of a derived category, from its cohomology

Let `𝒜` be an abelian category, `K` an object of `D(𝒜)` with cohomology in degrees `[a, b]` and
`L` any object of `D(𝒜)`.  If for every `q ∈ [a, b]` the object `H^q(K)`, placed in degree `q`,
has no nonzero morphism to `L⟦n⟧` for any `n ≤ n₀`, then neither has `K`.  This is the
"details omitted" step of the proof of [Stacks, Tag 0G5J]: the vanishing of
`Hom(τ_{≥1} Rb_*Ω^a, Ω^a)` reduces to that of `Hom(R^qb_*Ω^a[-q], Ω^a)`.

## Main results

* `Stacks.DerivedCategoryHomVanishing.subsingleton_hom_shift_of_homology`: the statement above.
* `Stacks.DerivedCategoryHomVanishing.isGE_one_of_distTriang` and
  `Stacks.DerivedCategoryHomVanishing.isIso_homology_mor₂_of_distTriang`: the cone of a map
  `M[0] ⟶ B`, with `B` in degrees `≥ 0` and `H^0` of the map invertible, lies in degrees `≥ 1`
  and has the cohomology of `B` there.
* `Stacks.DerivedCategoryHomVanishing.subsingleton_hom_singleFunctor_shift_iff`: for `M, E` in
  `𝒜`, morphisms `M[-q] ⟶ E[0]⟦n⟧` are degree-`n + q` morphisms `M[0] ⟶ E[0]`, i.e.
  `Ext^{n+q}(M, E)`.

## Implementation notes

The proof is an induction on the length `b - a`, splitting off the top cohomology with the
truncation triangle `τ_{<b} K ⟶ K ⟶ τ_{≥b} K ⟶` of the canonical t-structure: by exactness of
`Hom(-, L⟦n⟧)` on it, a morphism out of `K` killed by `τ_{<b} K ⟶ K` factors through
`τ_{≥b} K`, which is `H^b(K)` placed in degree `b`.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory

namespace Stacks.DerivedCategoryHomVanishing

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Vanishing of a Hom set transfers along an isomorphism of sources. -/
theorem subsingleton_hom_of_iso {A A' B : DerivedCategory C} (e : A ≅ A')
    (h : Subsingleton (A' ⟶ B)) : Subsingleton (A ⟶ B) :=
  (Equiv.subsingleton_congr (Iso.homCongr e (Iso.refl B))).mpr h

/-- **The base case**: an object with cohomology in the single degree `a` is its cohomology
placed in degree `a`. -/
theorem subsingleton_hom_of_isGE_of_isLE_self (K B : DerivedCategory C) (a : ℤ) [K.IsGE a]
    [K.IsLE a]
    (h : Subsingleton ((singleFunctor C a).obj ((homologyFunctor C a).obj K) ⟶ B)) :
    Subsingleton (K ⟶ B) := by
  obtain ⟨Y, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  refine subsingleton_hom_of_iso (e ≪≫ (singleFunctor C a).mapIso ?_) h
  exact ((singleFunctorCompHomologyFunctorIso C a).app Y).symm ≪≫
    (homologyFunctor C a).mapIso e.symm

/-- Vanishing of morphisms out of `H^q` placed in degree `q` is invariant under a map inducing an
isomorphism on `H^q`. -/
private theorem subsingleton_hom_single_homology_iff {X Y : DerivedCategory C} (f : X ⟶ Y) (q : ℤ)
    [IsIso ((homologyFunctor C q).map f)] (B : DerivedCategory C) :
    Subsingleton ((singleFunctor C q).obj ((homologyFunctor C q).obj Y) ⟶ B) ↔
      Subsingleton ((singleFunctor C q).obj ((homologyFunctor C q).obj X) ⟶ B) :=
  Equiv.subsingleton_congr (Iso.homCongr
    ((singleFunctor C q).mapIso (asIso ((homologyFunctor C q).map f))).symm (Iso.refl B))

/-- **Morphisms out of a bounded object, from its cohomology.**  Let `K` have cohomology in
degrees `[a, b]`.  If, for every `q ∈ [a, b]` and every `n ≤ n₀`, the object `H^q(K)` placed in
degree `q` has no nonzero morphism to `L⟦n⟧`, then `K` has no nonzero morphism to `L⟦n⟧` for any
`n ≤ n₀`. -/
theorem subsingleton_hom_shift_of_homology (L : DerivedCategory C) (n₀ : ℤ) :
    ∀ (d : ℕ) (K : DerivedCategory C) (a : ℤ), K.IsGE a → K.IsLE (a + d) →
      (∀ q : ℤ, a ≤ q → q ≤ a + d → ∀ n : ℤ, n ≤ n₀ →
        Subsingleton ((singleFunctor C q).obj ((homologyFunctor C q).obj K) ⟶ L⟦n⟧)) →
      ∀ n : ℤ, n ≤ n₀ → Subsingleton (K ⟶ L⟦n⟧) := by
  intro d
  induction d with
  | zero =>
    intro K a hGE hLE h n hn
    have : K.IsLE a := by simpa using hLE
    exact subsingleton_hom_of_isGE_of_isLE_self K _ a (h a le_rfl (by simp) n hn)
  | succ d ih =>
    intro K a hGE hLE h n hn
    let b : ℤ := a + (d + 1 : ℕ)
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    have h₁GE : T.obj₁.IsGE a := by
      dsimp only [T]
      change TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a
      infer_instance
    have h₁LE : T.obj₁.IsLE (a + d) := by
      have : TStructure.t.IsLE T.obj₁ (b - 1) := by
        dsimp only [T]
        infer_instance
      exact TStructure.t.isLE_of_le _ (b - 1) (a + d) (by omega)
    have h₃GE : T.obj₃.IsGE b := by
      dsimp only [T]
      infer_instance
    have h₃LE : T.obj₃.IsLE b := by
      have : TStructure.t.IsLE K b := hLE
      dsimp only [T]
      change TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b
      infer_instance
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT (x - y) (by
      have hsub := (ih T.obj₁ a h₁GE h₁LE (fun q hq₁ hq₂ m hm => by
        have := StacksDraft.ExtremalDegrees.isIso_homology_truncLT b q (by omega) K
        exact (subsingleton_hom_single_homology_iff ((TStructure.t.truncLTι b).app K) q _).mp
          (h q hq₁ (by omega) m hm)) n hn)
      exact hsub.elim _ _)
    rw [(subsingleton_hom_of_isGE_of_isLE_self T.obj₃ (L⟦n⟧) b (by
        have := StacksDraft.ExtremalDegrees.isIso_homology_truncGE b b le_rfl K
        exact (subsingleton_hom_single_homology_iff ((TStructure.t.truncGEπ b).app K) b _).mpr
          (h b (by omega) le_rfl n hn))).elim g 0, comp_zero] at hg
    exact sub_eq_zero.mp hg

/-- **Morphisms from a shifted single object are `Ext` groups**: a morphism from `M` placed in
degree `q` to `L⟦n⟧` is a morphism of degree `n + q` from `M` placed in degree zero to `L`. -/
def homSingleFunctorShiftEquiv (M : C) (L : DerivedCategory C) (q n : ℤ) :
    ((singleFunctor C q).obj M ⟶ L⟦n⟧) ≃ ShiftedHom ((singleFunctor C 0).obj M) L (n + q) :=
  ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor (DerivedCategory C) q)).homEquiv).trans
    (Iso.homCongr (((singleFunctors C).shiftIso q 0 q (by simp)).app M)
      ((shiftFunctorAdd' (DerivedCategory C) n q (n + q) rfl).app L).symm)

/-- The degree reindexing of `homSingleFunctorShiftEquiv`, for subsingletons. -/
theorem subsingleton_hom_singleFunctor_shift_iff (M : C) (L : DerivedCategory C) (q n : ℤ) :
    Subsingleton ((singleFunctor C q).obj M ⟶ L⟦n⟧) ↔
      Subsingleton (ShiftedHom ((singleFunctor C 0).obj M) L (n + q)) :=
  Equiv.subsingleton_congr (homSingleFunctorShiftEquiv M L q n)

/-! ### The cone of a map out of an object placed in degree zero -/

section Cone

variable {M : C} {B Z : DerivedCategory C} {u : (singleFunctor C 0).obj M ⟶ B} {p : B ⟶ Z}
  {w : Z ⟶ ((singleFunctor C 0).obj M)⟦(1 : ℤ)⟧}

/-- An object receiving an epimorphism which is zero is zero. -/
private theorem isZero_of_epi_of_eq_zero {X Y : C} (f : X ⟶ Y) (_ : Epi f) (hf : f = 0) :
    IsZero Y :=
  (IsZero.iff_id_eq_zero Y).mpr ((cancel_epi f).mp (by rw [hf, zero_comp, comp_zero]))

/-- The object `M` placed in degree zero has no cohomology outside degree zero. -/
private theorem isZero_homology_single (k : ℤ) (hk : k ≠ 0) :
    IsZero ((homologyFunctor C k).obj ((singleFunctor C 0).obj M)) := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 k h
  · exact DerivedCategory.isZero_of_isLE _ 0 k h

/-- In a distinguished triangle `M[0] ⟶ B ⟶ Z ⟶ M[0]⟦1⟧`, the map `H^k(B) ⟶ H^k(Z)` is an
epimorphism for `k + 1 ≠ 0`. -/
private theorem epi_homology_mor₂_of_ne (hT : Triangle.mk u p w ∈ distTriang _) (k : ℤ)
    (hk : k + 1 ≠ 0) : Epi ((homologyFunctor C k).map p) :=
  (HomologySequence.epi_homologyMap_mor₂_iff _ hT k (k + 1) rfl).mpr
    ((isZero_homology_single (k + 1) hk).eq_of_tgt _ _)

/-- **The cone of a map out of an object placed in degree zero, in positive degrees.**  For a
distinguished triangle `M[0] ⟶ B ⟶ Z ⟶ M[0]⟦1⟧`, the map `H^k(B) ⟶ H^k(Z)` is invertible for
every `k ≥ 1`. -/
theorem isIso_homology_mor₂_of_distTriang (hT : Triangle.mk u p w ∈ distTriang _) (k : ℤ)
    (hk : 1 ≤ k) : IsIso ((homologyFunctor C k).map p) := by
  have hm : Mono ((homologyFunctor C k).map p) :=
    (HomologySequence.mono_homologyMap_mor₂_iff _ hT k).mpr
      ((isZero_homology_single k (by omega)).eq_of_src _ _)
  have := epi_homology_mor₂_of_ne hT k (by omega)
  exact isIso_of_mono_of_epi _

/-- **The cone of a map out of an object placed in degree zero, in degrees `≤ 0`.**  For a
distinguished triangle `M[0] ⟶ B ⟶ Z ⟶ M[0]⟦1⟧` with `B` in degrees `≥ 0` and
`H^0(M[0]) ⟶ H^0(B)` invertible, `Z` is in degrees `≥ 1`. -/
theorem isGE_one_of_distTriang (hT : Triangle.mk u p w ∈ distTriang _) [B.IsGE 0]
    (hu : IsIso ((homologyFunctor C 0).map u)) : Z.IsGE 1 := by
  rw [DerivedCategory.isGE_iff]
  intro k hk
  rcases lt_trichotomy k (-1) with h | h | h
  · -- `k ≤ -2`: both neighbours vanish
    exact isZero_of_epi_of_eq_zero _ (epi_homology_mor₂_of_ne hT k (by omega))
      ((DerivedCategory.isZero_of_isGE B 0 k (by omega)).eq_of_src _ _)
  · -- `k = -1`: the connecting map into `H^0(M)` vanishes, `H^0(u)` being a monomorphism
    subst h
    have hδ : HomologySequence.δ _ (-1) 0 = 0 :=
      (HomologySequence.mono_homologyMap_mor₁_iff (Triangle.mk u p w) hT (-1) 0).mp
        (inferInstanceAs (Mono ((homologyFunctor C 0).map u)))
    have he : Epi ((homologyFunctor C (-1)).map p) :=
      (HomologySequence.epi_homologyMap_mor₂_iff _ hT (-1) 0 rfl).mpr hδ
    exact isZero_of_epi_of_eq_zero _ he
      ((DerivedCategory.isZero_of_isGE B 0 (-1) (by omega)).eq_of_src _ _)
  · -- `k = 0`: `H^0(u)` is an epimorphism, so `H^0(p)` is zero and epi
    obtain rfl : k = 0 := by omega
    exact isZero_of_epi_of_eq_zero _ (epi_homology_mor₂_of_ne hT 0 (by omega))
      ((HomologySequence.epi_homologyMap_mor₁_iff (Triangle.mk u p w) hT 0).mp
        (inferInstanceAs (Epi ((homologyFunctor C 0).map u))))

end Cone

end Stacks.DerivedCategoryHomVanishing

end
