module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Homology.WeakSerreRightDerivedOfAcyclicComplex

/-!
# Right derived functors through a resolution of the functor

Let `T : D ⥤ E` be an additive, left exact functor between abelian categories, `D` having
enough injectives, and let `Φ : D ⥤ CochainComplex E ℕ` be a functor whose components
`Φ_p = Φ ⋙ eval p` are additive and left exact, together with an augmentation
`ε : T ⟶ Φ_0` exhibiting `T M` as the kernel of `Φ_0 M ⟶ Φ_1 M` for every `M`.  Suppose that
for every injective `I` the complex `Φ I` is exact in positive degrees: the augmented complex
`0 ⟶ T ⟶ Φ_0 ⟶ Φ_1 ⟶ ⋯` is then a resolution of `T` on injectives.  If `M` is
`Φ_p`-acyclic for every `p`, then `RⁿT(M)` vanishes as soon as `Hⁿ(Φ M)` does, for `n ≥ 1`.

This is the statement that a resolution of a functor by acyclic functors computes its derived
functors, in the form in which it is used to compute cohomology by an alternating Čech
complex: `T` is global sections and `Φ_p` is the functor of alternating Čech cochains in degree
`p`.  No spectral sequence is used: the proof is dimension shifting along
`0 ⟶ M ⟶ I ⟶ M' ⟶ 0` for an injective `I`, which preserves the acyclicity hypothesis and along
which both `R^•T` and `H^•(Φ -)` shift by one, the first by the long exact sequence of right
derived functors and the second by the long exact homology sequence of
`0 ⟶ Φ M ⟶ Φ I ⟶ Φ M' ⟶ 0`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_obj_of_retract`: the right derived
  functors of a retract of a functor `G` vanish wherever those of `G` do.
* `Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_homology`: if `M` is
  `Φ_p`-acyclic for every `p` and `Hⁿ(Φ M) = 0` with `n ≥ 1`, then `RⁿT(M) = 0`.
* `Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_X`: if moreover the
  terms `(Φ M)ᵖ` vanish for `p ≥ d`, then `RⁿT(M) = 0` for every `n ≥ d`.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {D : Type u₁} [Category.{v₁} D] [Abelian D] [EnoughInjectives D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

/-- An additive left exact functor carries a short exact sequence whose first term has vanishing
first right derived functor to a short exact sequence. -/
theorem shortExact_map_of_isZero_rightDerived_one (F : D ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex D} (hS : S.ShortExact)
    (h1 : IsZero ((F.rightDerived 1).obj S.X₁)) : (S.map F).ShortExact := by
  obtain ⟨hex, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp inferInstance S hS
  have hδ : (rδ F).δ hS 0 = 0 := h1.eq_of_tgt _ _
  have hepi0 : Epi ((F.rightDerived 0).map S.g) := ((rδ F).exact_δ₁ hS 0).epi_f hδ
  have hepi : Epi (F.map S.g) := by
    have h := F.rightDerivedZeroIsoSelf.hom.naturality S.g
    have : F.map S.g = (F.rightDerivedZeroIsoSelf.inv.app S.X₂ ≫
        (F.rightDerived 0).map S.g) ≫ F.rightDerivedZeroIsoSelf.hom.app S.X₃ := by
      rw [assoc, h, ← assoc, Iso.inv_hom_id_app, id_comp]
    rw [this]
    infer_instance
  exact ShortComplex.ShortExact.mk' hex hmono hepi

/-- **A retract of a functor has retracts for right derived functors**: if `F` is a retract of
`G` and `RⁿG(M) = 0`, then `RⁿF(M) = 0`. -/
theorem isZero_rightDerived_obj_of_retract {F G : D ⥤ E} [F.Additive] [G.Additive]
    (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F) (n : ℕ) (M : D)
    (hG : IsZero ((G.rightDerived n).obj M)) : IsZero ((F.rightDerived n).obj M) := by
  have h1 : (NatTrans.rightDerived i n).app M ≫ (NatTrans.rightDerived r n).app M = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, h, NatTrans.rightDerived_id]
    rfl
  rw [IsZero.iff_id_eq_zero, ← h1, hG.eq_of_tgt ((NatTrans.rightDerived i n).app M) 0, zero_comp]

/-- Isomorphic functors have isomorphic right derived functors, object by object; in the
vanishing form. -/
theorem isZero_rightDerived_obj_of_iso {F G : D ⥤ E} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) (M : D) (hF : IsZero ((F.rightDerived n).obj M)) :
    IsZero ((G.rightDerived n).obj M) :=
  isZero_rightDerived_obj_of_retract e.inv e.hom e.inv_hom_id n M hF

variable (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]
  (Φ : D ⥤ CochainComplex E ℕ)

/-- The `p`-th component `M ↦ (Φ M)ᵖ` of a functor to cochain complexes. -/
abbrev component (p : ℕ) : D ⥤ E := Φ ⋙ HomologicalComplex.eval E (ComplexShape.up ℕ) p

variable [Φ.Additive] [∀ p, PreservesFiniteLimits (component Φ p)]

/-- An object is acyclic for every component of `Φ`. -/
def IsComponentAcyclic (M : D) : Prop :=
  ∀ p q : ℕ, 0 < q → IsZero (((component Φ p).rightDerived q).obj M)

/-- A short exact sequence of `D` whose first term is acyclic for every component of `Φ` is
carried by `Φ` to a short exact sequence of cochain complexes. -/
theorem shortExact_map_of_isComponentAcyclic {S : ShortComplex D} (hS : S.ShortExact)
    (hM : IsComponentAcyclic Φ S.X₁) : (S.map Φ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    (shortExact_map_of_isZero_rightDerived_one (component Φ p) hS (hM p 1 one_pos) :)

omit [∀ p, PreservesFiniteLimits (component Φ p)] in
/-- In a short exact sequence `0 ⟶ M ⟶ I ⟶ M' ⟶ 0` with `I` injective, if `M` is acyclic for
every component of `Φ` then so is `M'`. -/
theorem isComponentAcyclic_X₃ {S : ShortComplex D} (hS : S.ShortExact) [Injective S.X₂]
    (hM : IsComponentAcyclic Φ S.X₁) : IsComponentAcyclic Φ S.X₃ := by
  intro p q hq
  have hS' := (rδ (component Φ p)).exact_δ₁ hS q
  have hI : IsZero (((component Φ p).rightDerived q).obj S.X₂) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (component Φ p).isZero_rightDerived_obj_injective_succ k _
  exact hS'.isZero_X₂ (hI.eq_of_src _ _) ((hM p (q + 1) (Nat.succ_pos q)).eq_of_tgt _ _)

variable (ε : T ⟶ component Φ 0)
  (hw : ∀ M, ε.app M ≫ (Φ.obj M).d 0 1 = 0)

/-- The augmentation, read as a map to the cohomology of `Φ M` in degree `0`. -/
noncomputable def augmentationToHomology (M : D) : T.obj M ⟶ (Φ.obj M).homology 0 :=
  (Φ.obj M).liftCycles (ε.app M) 1 (by simp) (hw M) ≫ (Φ.obj M).homologyπ 0

omit [Abelian D] [EnoughInjectives D] [T.Additive] [PreservesFiniteLimits T] [Φ.Additive]
  [∀ p, PreservesFiniteLimits (component Φ p)] in
/-- The augmentation to degree-`0` cohomology is natural in `M`: it commutes with `T.map f` and
the map induced by `Φ.map f` on `H⁰`. -/
theorem augmentationToHomology_naturality {M N : D} (f : M ⟶ N) :
    augmentationToHomology T Φ ε hw M ≫ HomologicalComplex.homologyMap (Φ.map f) 0 =
      T.map f ≫ augmentationToHomology T Φ ε hw N := by
  simp only [augmentationToHomology, assoc, HomologicalComplex.homologyπ_naturality]
  rw [← assoc, ← assoc]
  congr 1
  rw [← cancel_mono ((Φ.obj N).iCycles 0)]
  simp only [assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i_assoc,
    HomologicalComplex.liftCycles_i]
  exact (ε.naturality f).symm

omit [Abelian D] [EnoughInjectives D] [T.Additive] [PreservesFiniteLimits T] [Φ.Additive]
  [∀ p, PreservesFiniteLimits (component Φ p)] in
/-- If `ε_M` is a monomorphism and `0 ⟶ T M ⟶ (Φ M)⁰ ⟶ (Φ M)¹` is exact, then the augmentation
`T M ⟶ H⁰(Φ M)` is an isomorphism. -/
theorem isIso_augmentationToHomology (M : D) (hmono : Mono (ε.app M))
    (hex : (ShortComplex.mk (ε.app M) ((Φ.obj M).d 0 1) (hw M)).Exact) :
    IsIso (augmentationToHomology T Φ ε hw M) := by
  have hπ : IsIso ((Φ.obj M).homologyπ 0) :=
    (Φ.obj M).isIso_homologyπ 0 0 (by simp) (by simp)
  have hk : IsLimit (KernelFork.ofι (ε.app M) (hw M)) := hex.fIsKernel
  have hc : IsLimit (KernelFork.ofι ((Φ.obj M).iCycles 0) ((Φ.obj M).iCycles_d 0 1)) :=
    (Φ.obj M).cyclesIsKernel 0 1 (by simp)
  have hlift : IsIso ((Φ.obj M).liftCycles (ε.app M) 1 (by simp) (hw M)) := by
    have he : (IsLimit.conePointUniqueUpToIso hk hc).hom =
        (Φ.obj M).liftCycles (ε.app M) 1 (by simp) (hw M) := by
      rw [← cancel_mono ((Φ.obj M).iCycles 0), HomologicalComplex.liftCycles_i]
      simpa using IsLimit.conePointUniqueUpToIso_hom_comp hk hc WalkingParallelPair.zero
    rw [← he]
    infer_instance
  unfold augmentationToHomology
  infer_instance

variable (hmono : ∀ M, Mono (ε.app M))
  (hex : ∀ M, (ShortComplex.mk (ε.app M) ((Φ.obj M).d 0 1) (hw M)).Exact)
  (hinj : ∀ (I : D) [Injective I] (n : ℕ), 0 < n → (Φ.obj I).ExactAt n)

include hmono hex hinj in
/-- **A resolution of `T` by acyclic functors computes `R^•T`, in the vanishing form.**  If `M`
is acyclic for every component of `Φ` and `Φ M` is exact in degree `n ≥ 1`, then
`RⁿT(M) = 0`. -/
theorem isZero_rightDerived_of_isZero_homology (n : ℕ) (hn : 0 < n) :
    ∀ M : D, IsComponentAcyclic Φ M → (Φ.obj M).ExactAt n →
      IsZero ((T.rightDerived n).obj M) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
  intro M hM hMn
  let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have : Injective S.X₂ := Injective.injective_under M
  have hΦS := shortExact_map_of_isComponentAcyclic Φ hS hM
  have hM' := isComponentAcyclic_X₃ Φ hS hM
  have hRI : ∀ q, 0 < q → IsZero ((T.rightDerived q).obj S.X₂) := fun q hq => by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact T.isZero_rightDerived_obj_injective_succ k _
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- `R¹T(M)` is the cokernel of `T(I) ⟶ T(M')`, which is onto because
    -- `H⁰(Φ I) ⟶ H⁰(Φ M')` is, as `H¹(Φ M) = 0`
    have hH1 : IsZero ((S.map Φ).X₁.homology 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hMn
    have hepiH : Epi (HomologicalComplex.homologyMap (S.map Φ).g 0) :=
      (hΦS.homology_exact₃ 0 1 (by simp)).epi_f (hH1.eq_of_tgt _ _)
    have : IsIso (augmentationToHomology T Φ ε hw S.X₂) :=
      isIso_augmentationToHomology T Φ ε hw _ (hmono _) (hex _)
    have : IsIso (augmentationToHomology T Φ ε hw S.X₃) :=
      isIso_augmentationToHomology T Φ ε hw _ (hmono _) (hex _)
    have hepiT : Epi (T.map S.g) := by
      have h := augmentationToHomology_naturality T Φ ε hw S.g
      have : T.map S.g = (augmentationToHomology T Φ ε hw S.X₂ ≫
          HomologicalComplex.homologyMap (Φ.map S.g) 0) ≫
            inv (augmentationToHomology T Φ ε hw S.X₃) := by
        rw [h, assoc, IsIso.hom_inv_id, comp_id]
      rw [this]
      have : Epi (HomologicalComplex.homologyMap (Φ.map S.g) 0) := hepiH
      infer_instance
    have hepi0 : Epi ((T.rightDerived 0).map S.g) :=
      epi_rightDerived_zero_map T S.g hepiT
    have hδ : (rδ T).δ hS 0 = 0 := ((rδ T).exact_δ₁ hS 0).epi_f_iff.1 hepi0
    exact ((rδ T).exact_δ₂ hS 0).isZero_X₂ hδ ((hRI 1 one_pos).eq_of_tgt _ _)
  · -- `R^{n+1}T(M) ≅ RⁿT(M')` and `H^{n+1}(Φ M) ≅ Hⁿ(Φ M')`
    have hHM' : (Φ.obj S.X₃).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      have hH : IsZero ((S.map Φ).X₁.homology (n + 1)) :=
        (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hMn
      have hHI : IsZero ((S.map Φ).X₂.homology n) :=
        (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hinj S.X₂ n hn0)
      have := (hΦS.homology_exact₃ n (n + 1) rfl)
      have hmono' : Mono (hΦS.δ n (n + 1) rfl) := this.mono_g (hHI.eq_of_src _ _)
      exact IsZero.of_mono (hΦS.δ n (n + 1) rfl) hH
    have hRM' := ih hn0 S.X₃ hM' hHM'
    exact ((rδ T).exact_δ₂ hS n).isZero_X₂ (hRM'.eq_of_src _ _)
      ((hRI (n + 1) (Nat.succ_pos n)).eq_of_tgt _ _)

include hmono hex hinj in
/-- **A resolution of `T` by acyclic functors of length `d` bounds the cohomological dimension.**
If `M` is acyclic for every component of `Φ` and the terms `(Φ M)ᵖ` vanish for `p ≥ d`, then
`RⁿT(M) = 0` for every `n ≥ d`. -/
theorem isZero_rightDerived_of_isZero_X (M : D) (hM : IsComponentAcyclic Φ M) (d : ℕ)
    (hd : ∀ p, d ≤ p → IsZero ((Φ.obj M).X p)) (n : ℕ) (hn : d ≤ n) :
    IsZero ((T.rightDerived n).obj M) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hd0 : d = 0 := Nat.le_zero.1 hn
    subst hd0
    have : Mono (ε.app M) := hmono M
    have h0 : IsZero (T.obj M) := IsZero.of_mono (ε.app M) (hd 0 le_rfl)
    exact IsZero.of_iso h0 (T.rightDerivedZeroIsoSelf.app M)
  · refine isZero_rightDerived_of_isZero_homology T Φ ε hw hmono hex hinj n hn0 M hM ?_
    exact HomologicalComplex.ExactAt.of_isZero (hd n hn)

end Stacks.Cohomology.RightDerivedCoEdge
