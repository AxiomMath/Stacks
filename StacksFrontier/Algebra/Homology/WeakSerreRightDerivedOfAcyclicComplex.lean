module

public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Right derived functors of the zeroth cohomology of an acyclic complex in a weak Serre class

Let `T : D ⥤ E` be an additive, left exact functor between abelian categories, `D` having enough
injectives, and let `K` be a cochain complex in `D`, indexed by `ℕ`, all of whose terms are
`T`-acyclic and such that `T K` is exact in every positive degree.  Let `P` be a property of
objects of `D` satisfied by every cohomology object of `K`, let `Q` be a weak Serre class of `E`,
and suppose that `RⁱT` carries `P` into `Q` for every `i ≤ n`.  Then `Rⁿ⁺¹T(H⁰ K)` lies in `Q`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_one_cycles`: `R¹T(Zᵏ) = 0` for every
  `k`, when `T K` is exact in positive degrees.
* `Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_cycles`: `RʲT(Zᵏ)` lies in `Q` for
  `1 ≤ j ≤ n + 1` and every `k`.
* `Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_succ_homology_zero`: `Rⁿ⁺¹T(H⁰ K)`
  lies in `Q`.
* `Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_succ_of_shortExact`: dimension shifting
  in a weak Serre class.
* `Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map`: `RⁿT` carries `P`
  into `Q` for every `n`, through an embedding of the objects with `P` into direct images.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Stacks.RightDerivedComp
open scoped ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]
  [EnoughInjectives D] (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]
  (K : CochainComplex D ℕ)

/-- The short exact sequence `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Bᵏ⁺¹ ⟶ 0`. -/
abbrev cyclesSES (k : ℕ) : ShortComplex D :=
  ShortComplex.mk (K.iCycles k) (cokernel.π (K.iCycles k)) (cokernel.condition (K.iCycles k))

/-- The short exact sequence `0 ⟶ Bᵏ⁺¹ ⟶ Zᵏ⁺¹ ⟶ Hᵏ⁺¹ ⟶ 0`. -/
abbrev boundariesSES (k : ℕ) : ShortComplex D :=
  ShortComplex.mk (boundariesToCycles K k (k + 1)) (K.homologyπ (k + 1))
    (boundariesToCycles_comp_homologyπ K k (k + 1))

omit [EnoughInjectives D] in
/-- The sequence `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Bᵏ⁺¹ ⟶ 0` is short exact. -/
lemma cyclesSES_shortExact (k : ℕ) : (cyclesSES K k).ShortExact := shortExact_cycles K k

omit [EnoughInjectives D] in
/-- The sequence `0 ⟶ Bᵏ⁺¹ ⟶ Zᵏ⁺¹ ⟶ Hᵏ⁺¹ ⟶ 0` is short exact. -/
lemma boundariesSES_shortExact (k : ℕ) : (boundariesSES K k).ShortExact :=
  shortExact_boundaries K k (k + 1) rfl

/-- The long exact sequence of the right derived functors of `T`. -/
abbrev rδ : CategoryTheory.DeltaFunctor D E :=
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T

omit [PreservesFiniteLimits T] in
/-- The `j`-th functor of `rδ T` is the `j`-th right derived functor of `T`. -/
lemma rδ_functor (j : ℕ) : (rδ T).functor j = T.rightDerived j := rfl

variable {K}

omit [EnoughInjectives D] in
/-- When `T K` is exact in degree `k + 1`, `T` applied to `Kᵏ ⟶ Zᵏ⁺¹` is an epimorphism. -/
lemma epi_map_toCycles (k : ℕ)
    (hK : IsZero (((T.mapHomologicalComplex _).obj K).homology (k + 1))) :
    Epi (T.map (K.toCycles k (k + 1))) := by
  have hepi : Epi (((T.mapHomologicalComplex _).obj K).toCycles k (k + 1)) := by
    refine Preadditive.epi_of_cancel_zero _ (fun {Z} g hg => ?_)
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
      (((T.mapHomologicalComplex _).obj K).homologyIsCokernel k (k + 1) (by simp)) g hg
    have h0 : ((T.mapHomologicalComplex _).obj K).homologyπ (k + 1) = 0 := hK.eq_of_tgt _ _
    rw [← hl]
    change ((T.mapHomologicalComplex _).obj K).homologyπ (k + 1) ≫ l = 0
    rw [h0, zero_comp]
  rw [← toCycles_comp_mapCyclesIso_inv T K k (k + 1)]
  infer_instance

omit [EnoughInjectives D] in
/-- When `T K` is exact in degree `k + 1`, `T(Kᵏ) ⟶ T(Bᵏ⁺¹)` is an epimorphism and
`T(Bᵏ⁺¹) ⟶ T(Zᵏ⁺¹)` an isomorphism. -/
lemma epi_map_π_and_isIso_map_boundariesToCycles (k : ℕ)
    (hK : IsZero (((T.mapHomologicalComplex _).obj K).homology (k + 1))) :
    Epi (T.map (cokernel.π (K.iCycles k))) ∧ IsIso (T.map (boundariesToCycles K k (k + 1))) := by
  have h := epi_map_toCycles T k hK
  rw [← π_comp_boundariesToCycles K k (k + 1), T.map_comp] at h
  have := mono_boundariesToCycles K k (k + 1) rfl
  have : Epi (T.map (boundariesToCycles K k (k + 1))) :=
    epi_of_epi (T.map (cokernel.π (K.iCycles k))) _
  have hiso : IsIso (T.map (boundariesToCycles K k (k + 1))) := isIso_of_mono_of_epi _
  exact ⟨(epi_comp_iff_of_isIso _ _).1 h, hiso⟩

/-- An epimorphism stays an epimorphism under the zeroth right derived functor, which is
isomorphic to the functor itself. -/
lemma epi_rightDerived_zero_map {X Y : D} (f : X ⟶ Y) (hf : Epi (T.map f)) :
    Epi ((T.rightDerived 0).map f) := by
  have h := T.rightDerivedZeroIsoSelf.hom.naturality f
  have : (T.rightDerived 0).map f =
      (T.rightDerivedZeroIsoSelf.hom.app X ≫ T.map f) ≫ T.rightDerivedZeroIsoSelf.inv.app Y := by
    rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [this]
  infer_instance

variable (hX : ∀ q, acyclic T (K.X q))
  (hK : ∀ q, 0 < q → IsZero (((T.mapHomologicalComplex _).obj K).homology q))

include hX hK in
/-- **`R¹T(Zᵏ) = 0`** for a complex of `T`-acyclic objects whose image under `T` is exact in
positive degrees. -/
lemma isZero_rightDerived_one_cycles (k : ℕ) :
    IsZero ((T.rightDerived 1).obj (K.cycles k)) := by
  have hS := cyclesSES_shortExact K k
  have hepi : Epi ((T.rightDerived 0).map (cokernel.π (K.iCycles k))) :=
    epi_rightDerived_zero_map T _
      (epi_map_π_and_isIso_map_boundariesToCycles T k (hK (k + 1) (Nat.succ_pos k))).1
  have : Mono ((T.rightDerived 1).map (K.iCycles k)) :=
    ((rδ T).exact_δ₂ hS 0).mono_g_iff.2 (((rδ T).exact_δ₁ hS 0).epi_f_iff.1 hepi)
  exact IsZero.of_mono ((T.rightDerived 1).map (K.iCycles k)) (hX k 1 one_pos)

omit [PreservesFiniteLimits T] in
include hX hK in
/-- `RʲT(Bᵏ⁺¹) ≅ Rʲ⁺¹T(Zᵏ)` for `j ≥ 1`, the middle term `Kᵏ` being `T`-acyclic: the connecting
morphism of `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Bᵏ⁺¹ ⟶ 0` is invertible. -/
lemma isIso_δ_cyclesSES (k j : ℕ) (hj : 1 ≤ j) :
    IsIso ((rδ T).δ (cyclesSES_shortExact K k) j) := by
  have hS := cyclesSES_shortExact K k
  have : Mono ((rδ T).δ hS j) := ((rδ T).exact_δ₁ hS j).mono_g ((hX k j hj).eq_of_src _ _)
  have : Epi ((rδ T).δ hS j) :=
    ((rδ T).exact_δ₂ hS j).epi_f ((hX k (j + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

section CoEdge

variable (P : ObjectProperty D) (Q : ObjectProperty E) [Q.IsWeakSerreClass]

include hX hK in
/-- **`RʲT(Zᵏ)` lies in `Q` for `j ≥ 1` and `j + k ≤ n + 1`**, when the cohomology objects of
`K` in degrees `≤ n` satisfy `P` and `RⁱT` carries `P` into `Q` for `i ≤ n`. -/
theorem prop_rightDerived_cycles (n : ℕ) (hP : ∀ q ≤ n, P (K.homology q))
    (hQ : ∀ i ≤ n, ∀ M, P M → Q ((T.rightDerived i).obj M)) :
    ∀ j k, 1 ≤ j → j + k ≤ n + 1 → Q ((T.rightDerived j).obj (K.cycles k)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro k hj1 hjn
  have : (T.rightDerived 0).Additive := (rδ T).additive 0
  obtain _ | _ | m := j
  · omega
  · exact Q.prop_of_isZero (isZero_rightDerived_one_cycles T hX hK k)
  have hδ := isIso_δ_cyclesSES T hX hK k (m + 1) (by omega)
  refine Q.prop_of_iso (@asIso _ _ _ _ ((rδ T).δ (cyclesSES_shortExact K k) (m + 1)) hδ) ?_
  change Q ((T.rightDerived (m + 1)).obj (cokernel (K.iCycles k)))
  have hB := boundariesSES_shortExact K k
  have e₁ := (rδ T).exact_δ₂ hB m
  have e₂ := (rδ T).exact_map hB (m + 1)
  obtain _ | m := m
  · have hzero : (T.rightDerived 0).map (K.homologyπ (k + 1)) = 0 := by
      have hepi : Epi ((T.rightDerived 0).map (boundariesToCycles K k (k + 1))) :=
        epi_rightDerived_zero_map T _ (by
          have := (epi_map_π_and_isIso_map_boundariesToCycles T k
            (hK (k + 1) (Nat.succ_pos k))).2
          infer_instance)
      rw [← cancel_epi ((T.rightDerived 0).map (boundariesToCycles K k (k + 1))),
        ← Functor.map_comp, boundariesToCycles_comp_homologyπ, Functor.map_zero, comp_zero]
    have hmono : Mono ((rδ T).δ hB 0) := ((rδ T).exact_δ₁ hB 0).mono_g hzero
    exact ObjectProperty.prop_mid_of_exact₄ (P := Q) (fun S hS => Q.prop_obj₂_of_exact S hS)
      (f₀ := (0 : (0 : E) ⟶ (T.rightDerived 0).obj (K.homology (k + 1))))
      zero_comp ((rδ T).δ_map_f hB 0) ((rδ T).map_f_comp_map_g 1)
      ((ShortComplex.exact_iff_mono _ rfl).2 hmono) e₁ e₂
      (Q.prop_of_isZero (isZero_zero E)) (hQ 0 (by omega) _ (hP _ (by omega)))
      (Q.prop_of_isZero (isZero_rightDerived_one_cycles T hX hK (k + 1)))
      (hQ 1 (by omega) _ (hP _ (by omega)))
  · exact ObjectProperty.prop_mid_of_exact₄ (P := Q) (fun S hS => Q.prop_obj₂_of_exact S hS)
      ((rδ T).map_g_δ hB (m + 1)) ((rδ T).δ_map_f hB (m + 1))
      ((rδ T).map_f_comp_map_g (m + 2)) ((rδ T).exact_δ₁ hB (m + 1)) e₁ e₂
      (ih (m + 1) (by omega) (k + 1) (by omega) (by omega))
      (hQ (m + 1) (by omega) _ (hP _ (by omega)))
      (ih (m + 2) (by omega) (k + 1) (by omega) (by omega))
      (hQ (m + 2) (by omega) _ (hP _ (by omega)))

include hX hK in
/-- **`Rⁿ⁺¹T(H⁰ K)` lies in `Q`**, when the cohomology objects of `K` in degrees `≤ n` satisfy `P`
and `RⁱT` carries `P` into `Q` for `i ≤ n`. -/
theorem prop_rightDerived_succ_homology_zero (n : ℕ) (hP : ∀ q ≤ n, P (K.homology q))
    (hQ : ∀ i ≤ n, ∀ M, P M → Q ((T.rightDerived i).obj M)) :
    Q ((T.rightDerived (n + 1)).obj (K.homology 0)) :=
  Q.prop_of_iso ((T.rightDerived (n + 1)).mapIso (CochainComplex.isoHomologyπ₀ K))
    (prop_rightDerived_cycles T hX hK P Q n hP hQ (n + 1) 0 (by omega) le_rfl)

end CoEdge

/-! ### Dimension shifting in a weak Serre class -/

section DimensionShifting

variable (Q : ObjectProperty E) [Q.IsWeakSerreClass]

/-- If `g ≫ δ = 0` is exact in the middle and `δ ≫ a = 0`, then it stays exact when `δ` is
corestricted to `kernel a`. -/
private theorem exact_mk_kernel_lift {A B C D : E} {g : A ⟶ B} {δ : B ⟶ C} (a : C ⟶ D)
    (hδ : δ ≫ a = 0) (hgδ : g ≫ δ = 0) (e : (ShortComplex.mk g δ hgδ).Exact) :
    (ShortComplex.mk g (kernel.lift a δ hδ)
      (by rw [← cancel_mono (kernel.ι a)]; simp [hgδ])).Exact := by
  let ψ : ShortComplex.mk g (kernel.lift a δ hδ)
      (by rw [← cancel_mono (kernel.ι a)]; simp [hgδ]) ⟶ ShortComplex.mk g δ hgδ :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι a, comm₁₂ := by simp, comm₂₃ := by simp }
  have : Epi ψ.τ₁ := by dsimp [ψ]; infer_instance
  have : IsIso ψ.τ₂ := by dsimp [ψ]; infer_instance
  have : Mono ψ.τ₃ := by dsimp [ψ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 e

omit [PreservesFiniteLimits T] in
/-- For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, the kernel of `Rⁿ⁺¹T(A) ⟶ Rⁿ⁺¹T(B)` lies
in the weak Serre class `Q` as soon as `RⁿT(B)` and `RⁿT(C)` do. -/
theorem prop_kernel_rightDerived_succ_map_f {S : ShortComplex D} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Q ((T.rightDerived n).obj S.X₂)) (h₃ : Q ((T.rightDerived n).obj S.X₃)) :
    Q (kernel ((T.rightDerived (n + 1)).map S.f)) := by
  let δ' : (T.rightDerived n).obj S.X₃ ⟶ (T.rightDerived (n + 1)).obj S.X₁ := (rδ T).δ hS n
  have hδ : δ' ≫ (T.rightDerived (n + 1)).map S.f = 0 := (rδ T).δ_map_f hS n
  have hgδ : (T.rightDerived n).map S.g ≫ δ' = 0 := (rδ T).map_g_δ hS n
  have e₁ : (ShortComplex.mk _ _ hgδ).Exact := (rδ T).exact_δ₁ hS n
  have e₂ : (ShortComplex.mk _ _ hδ).Exact := (rδ T).exact_δ₂ hS n
  let l : (T.rightDerived n).obj S.X₃ ⟶ kernel ((T.rightDerived (n + 1)).map S.f) :=
    kernel.lift ((T.rightDerived (n + 1)).map S.f) δ' hδ
  have hl : Epi l := e₂.epi_kernelLift
  have e₁' := exact_mk_kernel_lift _ hδ hgδ e₁
  exact ObjectProperty.prop_mid_of_exact₄ (P := Q) (fun S hS => Q.prop_obj₂_of_exact S hS)
    (f₂ := (0 : _ ⟶ (0 : E))) (f₃ := (0 : (0 : E) ⟶ 0)) _ comp_zero comp_zero e₁'
    ((ShortComplex.exact_iff_epi _ rfl).2 hl)
    (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero E)) h₂ h₃
    (Q.prop_of_isZero (isZero_zero E)) (Q.prop_of_isZero (isZero_zero E))

omit [PreservesFiniteLimits T] in
/-- **Dimension shifting in a weak Serre class.**  Let `P` be a property of objects of `D` and
`Q` a weak Serre class of `E`.  Suppose `RⁿT` carries `P` into `Q`, and that every `M` with `P`
sits in a short exact sequence `0 ⟶ M ⟶ N ⟶ M' ⟶ 0` with `P M'` and with `RⁿT(N)` and `Rⁿ⁺¹T(N)`
in `Q`.  Then `Rⁿ⁺¹T` carries `P` into `Q`. -/
theorem prop_rightDerived_succ_of_shortExact (P : ObjectProperty D) (n : ℕ)
    (hn : ∀ M, P M → Q ((T.rightDerived n).obj M))
    (hemb : ∀ M, P M → ∃ (N M' : D) (i : M ⟶ N) (p : N ⟶ M') (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ P M' ∧
        Q ((T.rightDerived n).obj N) ∧ Q ((T.rightDerived (n + 1)).obj N)) :
    ∀ M, P M → Q ((T.rightDerived (n + 1)).obj M) := by
  intro M hM
  have : (T.rightDerived (n + 1)).Additive := (rδ T).additive (n + 1)
  obtain ⟨N, M', i, p, w, hS, hM', hN, hN'⟩ := hemb M hM
  obtain ⟨N₂, M₂, i₂, p₂, w₂, hS₂, hM₂, hN₂, hN₂'⟩ := hemb M' hM'
  let a := (T.rightDerived (n + 1)).map i
  let b := (T.rightDerived (n + 1)).map p
  let c := (T.rightDerived (n + 1)).map i₂
  have hA : Q (kernel c) := prop_kernel_rightDerived_succ_map_f T Q hS₂ n hN₂ (hn _ hM₂)
  have hK : Q (kernel (b ≫ c)) := Q.prop_kernel _ hN' hN₂'
  let φ : kernel (b ≫ c) ⟶ kernel c :=
    kernel.lift c (kernel.ι (b ≫ c) ≫ b) (by rw [Category.assoc, kernel.condition])
  let j : kernel b ⟶ kernel (b ≫ c) :=
    kernel.lift (b ≫ c) (kernel.ι b) (by rw [← Category.assoc, kernel.condition, zero_comp])
  have hj : j ≫ φ = 0 := by
    rw [← cancel_mono (kernel.ι c), Category.assoc, kernel.lift_ι, ← Category.assoc,
      kernel.lift_ι, kernel.condition, zero_comp]
  have hlim : IsLimit (KernelFork.ofι j hj) :=
    KernelFork.IsLimit.ofι _ _
      (fun g' hg' => kernel.lift b (g' ≫ kernel.ι (b ≫ c)) (by
        simpa [φ] using congrArg (· ≫ kernel.ι c) hg'))
      (fun g' hg' => by rw [← cancel_mono (kernel.ι (b ≫ c))]; simp [j])
      (fun g' hg' m hm => by
        rw [← cancel_mono (kernel.ι b), kernel.lift_ι, ← hm, Category.assoc, kernel.lift_ι])
  have e : kernel φ ≅ kernel b := IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) hlim
  have hkb : Q (kernel b) := Q.prop_of_iso e (Q.prop_kernel φ hK hA)
  let δ' : (T.rightDerived n).obj M' ⟶ (T.rightDerived (n + 1)).obj M := (rδ T).δ hS n
  have hδ : δ' ≫ a = 0 := (rδ T).δ_map_f hS n
  have hgδ : (T.rightDerived n).map p ≫ δ' = 0 := (rδ T).map_g_δ hS n
  have e₁ : (ShortComplex.mk _ _ hgδ).Exact := (rδ T).exact_δ₁ hS n
  have e₂ : (ShortComplex.mk _ _ hδ).Exact := (rδ T).exact_δ₂ hS n
  have hab : a ≫ b = 0 := by rw [← Functor.map_comp, w, Functor.map_zero]
  have e₃ : (ShortComplex.mk _ _ hab).Exact := (rδ T).exact_map hS (n + 1)
  let l : (T.rightDerived (n + 1)).obj M ⟶ kernel b := kernel.lift b a hab
  have hl : Epi l := e₃.epi_kernelLift
  have e₂' := exact_mk_kernel_lift b hab hδ e₂
  exact ObjectProperty.prop_mid_of_exact₄ (P := Q) (fun S hS => Q.prop_obj₂_of_exact S hS)
    (f₃ := (0 : kernel b ⟶ (0 : E))) hgδ _ comp_zero e₁ e₂'
    ((ShortComplex.exact_iff_epi _ rfl).2 hl) hN (hn _ hM') hkb
    (Q.prop_of_isZero (isZero_zero E))

end DimensionShifting

/-! ### Right derived functors through an exact embedding into direct images -/

section Embedding

variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
  (PC : ObjectProperty C) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
  (Q : ObjectProperty E) [Q.IsWeakSerreClass]

/-- **`Rⁿ⁺¹T(G H)` lies in `Q`**, when every `RᵠG(H)` satisfies `P`, the composite `G ⋙ T` has
vanishing higher right derived functors at `H`, and `RⁱT` carries `P` into `Q` for `i ≤ n`. -/
theorem prop_rightDerived_succ_obj_map (H : C) (n : ℕ)
    (hG : ∀ q ≤ n, P ((G.rightDerived q).obj H))
    (hGT : ∀ q, 0 < q → IsZero (((G ⋙ T).rightDerived q).obj H))
    (hQ : ∀ i ≤ n, ∀ M, P M → Q ((T.rightDerived i).obj M)) :
    Q ((T.rightDerived (n + 1)).obj (G.obj H)) := by
  let I := injectiveResolution H
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hX : ∀ q, acyclic T (K.X q) := fun q =>
    have := I.injective q
    have := G.injective_obj (I.cocomplex.X q)
    acyclic_of_injective T (G.obj (I.cocomplex.X q))
  have hK : ∀ q, 0 < q → IsZero (((T.mapHomologicalComplex _).obj K).homology q) := fun q hq =>
    IsZero.of_iso (hGT q hq)
      ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) q).mapIso
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ T)) _).app I.cocomplex) ≪≫
        (I.isoRightDerivedObj (G ⋙ T) q).symm)
  have hP : ∀ q ≤ n, P (K.homology q) := fun q hq =>
    P.prop_of_iso (I.isoRightDerivedObj G q) (hG q hq)
  exact Q.prop_of_iso ((T.rightDerived (n + 1)).mapIso
      ((I.isoRightDerivedObj G 0).symm ≪≫ G.rightDerivedZeroIsoSelf.app H))
    (prop_rightDerived_succ_homology_zero T hX hK P Q n hP hQ)

omit [Abelian C] [EnoughInjectives D] [EnoughInjectives C] [G.Additive]
  [PreservesFiniteLimits G] [G.PreservesInjectiveObjects] [P.IsClosedUnderIsomorphisms] in
/-- If every `M` with `P` embeds into some `G H` with `PC H` with cokernel in `P`, and `T(G H)`
lies in the weak Serre class `Q` for every `H` with `PC H`, then `T M` lies in `Q` for every `M`
with `P`. -/
theorem prop_obj_of_exists_mono_map
    (hGT₀ : ∀ H, PC H → Q (T.obj (G.obj H)))
    (hemb : ∀ M, P M → ∃ (H : C) (i : M ⟶ G.obj H), Mono i ∧ PC H ∧ P (cokernel i))
    (M : D) (hM : P M) : Q (T.obj M) := by
  obtain ⟨H₁, i₁, hi₁, hH₁, hC₁⟩ := hemb M hM
  obtain ⟨H₂, i₂, hi₂, hH₂, -⟩ := hemb _ hC₁
  have hlim : IsLimit (KernelFork.ofι i₁ (by simp) : KernelFork (cokernel.π i₁ ≫ i₂)) :=
    isKernelCompMono (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i₁)) i₂ rfl
  have e : T.obj M ≅ kernel (T.map (cokernel.π i₁ ≫ i₂)) :=
    IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ hlim T) (limit.isLimit _)
  exact Q.prop_of_iso e.symm (Q.prop_kernel _ (hGT₀ H₁ hH₁) (hGT₀ H₂ hH₂))

/-- **The induction step for right derived functors of `T` on `P` through an embedding into
direct images under `G`.**  Let `G : C ⥤ D` be left exact and preserve injectives, and
`T : D ⥤ E` be left exact.  Let `PC` and `P` be properties of objects of `C` and `D` and `Q` a weak
Serre class of `E`.  Suppose that for every `H` with `PC H` the `RᵠG(H)`, `q ≤ n`, satisfy `P`
and `Rᵠ(G ⋙ T)(H) = 0` for `q > 0`; that every `M` with `P` embeds into some `G H` with `PC H`
with cokernel in `P`; and that `RⁱT` carries `P` into `Q` for `i ≤ n`.  Then so does `Rⁿ⁺¹T`. -/
theorem prop_rightDerived_succ_of_exists_mono_map (n : ℕ)
    (hG : ∀ H, PC H → ∀ q ≤ n, P ((G.rightDerived q).obj H))
    (hGT : ∀ H, PC H → ∀ q, 0 < q → IsZero (((G ⋙ T).rightDerived q).obj H))
    (hemb : ∀ M, P M → ∃ (H : C) (i : M ⟶ G.obj H), Mono i ∧ PC H ∧ P (cokernel i))
    (hQ : ∀ i ≤ n, ∀ M, P M → Q ((T.rightDerived i).obj M)) :
    ∀ M, P M → Q ((T.rightDerived (n + 1)).obj M) := by
  refine prop_rightDerived_succ_of_shortExact T Q P n (hQ n le_rfl) fun M hM => ?_
  obtain ⟨H, i, hi, hH, hC⟩ := hemb M hM
  exact ⟨G.obj H, cokernel i, i, cokernel.π i, cokernel.condition i,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) hi inferInstance, hC,
    hQ n le_rfl _ (P.prop_of_iso (G.rightDerivedZeroIsoSelf.app H) (hG H hH 0 (Nat.zero_le n))),
    prop_rightDerived_succ_obj_map T G P Q H n (hG H hH) (hGT H hH) hQ⟩

/-- **Right derived functors of `T` on `P` through an embedding into direct images under `G`.**
With the notation of
`Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_succ_of_exists_mono_map`: if for every
`H` with `PC H` all `RᵠG(H)` satisfy `P`, `T(G H)` is in `Q` and `Rᵠ(G ⋙ T)(H) = 0` for `q > 0`,
and every `M` with `P` embeds into some `G H` with `PC H` with cokernel in `P`, then `RⁿT`
carries `P` into `Q` for every `n`. -/
theorem prop_rightDerived_of_exists_mono_map
    (hG : ∀ H, PC H → ∀ q, P ((G.rightDerived q).obj H))
    (hGT₀ : ∀ H, PC H → Q (T.obj (G.obj H)))
    (hGT : ∀ H, PC H → ∀ q, 0 < q → IsZero (((G ⋙ T).rightDerived q).obj H))
    (hemb : ∀ M, P M → ∃ (H : C) (i : M ⟶ G.obj H), Mono i ∧ PC H ∧ P (cokernel i)) :
    ∀ n M, P M → Q ((T.rightDerived n).obj M) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain _ | n := n
  · exact fun M hM => Q.prop_of_iso (T.rightDerivedZeroIsoSelf.app M).symm
      (prop_obj_of_exists_mono_map T G PC P Q hGT₀ hemb M hM)
  · exact prop_rightDerived_succ_of_exists_mono_map T G PC P Q n (fun H hH q _ => hG H hH q)
      hGT hemb fun i hi => ih i (by omega)

end Embedding

end Stacks.Cohomology.RightDerivedCoEdge

end
