module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso

/-!
# Exactness of a sequence of homologies of complexes of modules, from elementwise data

Let `K --φ--> L --ψ--> M` be morphisms of complexes of modules whose composite induces the zero
map on homology in a degree `i`.  In a degree with no incoming differential homology is the
kernel of the outgoing differential, and in a degree with no outgoing differential it is the
cokernel of the incoming one; in both cases exactness of

`Hⁱ(K) ⟶ Hⁱ(L) ⟶ Hⁱ(M)`

at the middle term is an elementwise condition on the three complexes.

The composite `φ ≫ ψ` is *not* assumed to be zero, only to induce zero on homology.

## Main results

* `CategoryTheory.epi_of_exact_of_exact_of_mono`: a map into the source of a monomorphism `v` is
  an epimorphism as soon as its composite with `v` and `v` itself have the same image, in the
  sense that both are exact against one and the same map out of the target of `v`.
* `HomologicalComplex.exact_homologyMap_of_exists_cycle`: exactness at `Hⁱ(L)` in a degree with
  no incoming differential into `M`, from the condition that every cycle of `L` in degree `i`
  killed by `ψ` is the image of a cycle of `K`.
* `HomologicalComplex.exact_homologyMap_of_exists_add_d`: exactness at `Hʲ(L)` in a degree with
  no outgoing differential out of `K`, from the condition that every element of `L` in degree
  `j` whose image under `ψ` is a boundary is the sum of an element of the image of `φ` and a
  boundary.
* `HomologicalComplex.epi_homologyMap_of_epi_opcyclesMap` and
  `HomologicalComplex.epi_opcyclesMap_of_surjective`: in a degree with no outgoing differential
  the map of homology is an epimorphism as soon as the map of opcycles is, and the latter holds as
  soon as it is surjective in elementary terms.
* `CochainComplex.exists_cycle_of_addEquiv` and `CochainComplex.exists_add_d_of_addEquiv`: those
  two elementwise conditions transported along additive identifications of the terms of the three
  complexes.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-- **A map whose composite with a monomorphism has the image that monomorphism has is an
epimorphism.**  If `v` is a monomorphism, if `(t, w)` and `(v, w)` are both exact and if
`u ≫ v = t`, then `u` is an epimorphism. -/
theorem epi_of_exact_of_exact_of_mono {C : Type*} [Category* C] [Abelian C] {A B D E : C}
    (u : A ⟶ B) (v : B ⟶ D) (w : D ⟶ E) (t : A ⟶ D) [Mono v] (ht : u ≫ v = t)
    (h₀ : t ≫ w = 0) (h₁ : v ≫ w = 0)
    (hex₁ : (ShortComplex.mk t w h₀).Exact) (hex₂ : (ShortComplex.mk v w h₁).Exact) :
    Epi u := by
  have : Epi (kernel.lift w t h₀) := (ShortComplex.exact_iff_epi_kernel_lift _).1 hex₁
  have : Epi (kernel.lift w v h₁) := (ShortComplex.exact_iff_epi_kernel_lift _).1 hex₂
  have : Mono (kernel.lift w v h₁) := mono_of_mono_fac (kernel.lift_ι w v h₁)
  have : IsIso (kernel.lift w v h₁) := isIso_of_mono_of_epi _
  rw [show u = kernel.lift w t h₀ ≫ inv (kernel.lift w v h₁) by
    rw [IsIso.eq_comp_inv]
    ext
    simp [ht]]
  infer_instance

end CategoryTheory

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L M : HomologicalComplex (ModuleCat.{v} R) c}

/-- **Exactness of `Hⁱ(K) ⟶ Hⁱ(L) ⟶ Hⁱ(M)` in a degree with no incoming differential into the
last complex**, from the elementwise condition that a cycle of `L` in degree `i` killed by `ψ`
is the image of a cycle of `K`. -/
theorem exact_homologyMap_of_exists_cycle (φ : K ⟶ L) (ψ : L ⟶ M) (i j k : ι)
    (hj : c.next i = j) (hk : c.prev i = k) (hdM : M.d k i = 0)
    (hzero : homologyMap φ i ≫ homologyMap ψ i = 0)
    (hex : ∀ y : L.X i, L.d i j y = 0 → ψ.f i y = 0 →
      ∃ x : K.X i, K.d i j x = 0 ∧ φ.f i x = y) :
    (ShortComplex.mk (homologyMap φ i) (homologyMap ψ i) hzero).Exact := by
  subst hj
  have hMπ := M.isIso_homologyπ k i hk hdM
  have hLπ : Function.Surjective (L.homologyπ i) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hLi : Function.Injective (L.iCycles i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hiψ : ∀ u : L.cycles i, M.iCycles i (cyclesMap ψ i u) = ψ.f i (L.iCycles i u) :=
    fun u ↦ congr($(cyclesMap_i ψ i) u)
  have hiφ : ∀ u : K.cycles i, L.iCycles i (cyclesMap φ i u) = φ.f i (K.iCycles i u) :=
    fun u ↦ congr($(cyclesMap_i φ i) u)
  have hπψ : ∀ u : L.cycles i,
      homologyMap ψ i (L.homologyπ i u) = M.homologyπ i (cyclesMap ψ i u) :=
    fun u ↦ congr($(homologyπ_naturality ψ i) u)
  have hπφ : ∀ u : K.cycles i,
      homologyMap φ i (K.homologyπ i u) = L.homologyπ i (cyclesMap φ i u) :=
    fun u ↦ congr($(homologyπ_naturality φ i) u)
  have hdi : ∀ u : L.cycles i, L.d i (c.next i) (L.iCycles i u) = 0 :=
    fun u ↦ congr($(L.iCycles_d i (c.next i)) u)
  refine (ShortComplex.moduleCat_exact_iff _).mpr fun b hb ↦ ?_
  obtain ⟨b', rfl⟩ := hLπ b
  have hb' : homologyMap ψ i (L.homologyπ i b') = 0 := hb
  have hψ : cyclesMap ψ i b' = 0 :=
    (ModuleCat.mono_iff_injective (M.homologyπ i)).mp inferInstance
      (by rw [map_zero, ← hπψ b', hb'])
  obtain ⟨x, hx, hxy⟩ := hex (L.iCycles i b') (hdi b')
    (by rw [← hiψ b', hψ, map_zero])
  obtain ⟨a, ha⟩ := K.exists_iCycles_eq i x hx
  have hcyc : cyclesMap φ i a = b' := hLi (by rw [hiφ a, ha, hxy])
  exact ⟨K.homologyπ i a, by rw [show (ShortComplex.mk (homologyMap φ i) (homologyMap ψ i)
    hzero).f = homologyMap φ i from rfl, hπφ a, hcyc]⟩

/-- If `φ x + d z = y`, then `x` and `y` have the same image in opcycles under `opcyclesMap φ`. -/
private theorem opcyclesMap_pOpcycles_eq_of_add_d (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    (x : K.X j) (z : L.X i) (y : L.X j) (h : φ.f j x + L.d i j z = y) :
    opcyclesMap φ j (K.pOpcycles j x) = L.pOpcycles j y := by
  subst hi h
  have h₁ : opcyclesMap φ j (K.pOpcycles j x) = L.pOpcycles j (φ.f j x) :=
    congr($(p_opcyclesMap φ j) x)
  have h₂ : L.pOpcycles j (L.d (c.prev j) j z) = 0 := congr($(L.d_pOpcycles (c.prev j) j) z)
  rw [h₁, map_add, h₂, add_zero]

/-- **Exactness of `Hʲ(K) ⟶ Hʲ(L) ⟶ Hʲ(M)` in a degree with no outgoing differential out of the
first complex**, from the elementwise condition that an element of `L` in degree `j` whose image
under `ψ` is a boundary differs from an element of the image of `φ` by a boundary. -/
theorem exact_homologyMap_of_exists_add_d (φ : K ⟶ L) (ψ : L ⟶ M) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) (hdK : K.d j k = 0)
    (hzero : homologyMap φ j ≫ homologyMap ψ j = 0)
    (hex : ∀ y : L.X j, (∃ w : M.X i, M.d i j w = ψ.f j y) →
      ∃ (x : K.X j) (z : L.X i), φ.f j x + L.d i j z = y) :
    (ShortComplex.mk (homologyMap φ j) (homologyMap ψ j) hzero).Exact := by
  subst hi
  have hKι := K.isIso_homologyι j k hk hdK
  have hKe : Function.Surjective (K.homologyι j) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hLp : Function.Surjective (L.pOpcycles j) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hpψ : ∀ y : L.X j, opcyclesMap ψ j (L.pOpcycles j y) = M.pOpcycles j (ψ.f j y) :=
    fun y ↦ congr($(p_opcyclesMap ψ j) y)
  have hιψ : ∀ u : L.homology j,
      M.homologyι j (homologyMap ψ j u) = opcyclesMap ψ j (L.homologyι j u) :=
    fun u ↦ congr($(homologyι_naturality ψ j) u)
  have hιφ : ∀ u : K.homology j,
      L.homologyι j (homologyMap φ j u) = opcyclesMap φ j (K.homologyι j u) :=
    fun u ↦ congr($(homologyι_naturality φ j) u)
  refine (ShortComplex.moduleCat_exact_iff _).mpr fun b hb ↦ ?_
  have hb' : homologyMap ψ j b = 0 := hb
  obtain ⟨y, hy⟩ := hLp (L.homologyι j b)
  obtain ⟨x, z, hxz⟩ := hex y (M.exists_d_eq_of_pOpcycles_eq_zero j (ψ.f j y)
    (by rw [← hpψ y, hy, ← hιψ b, hb', map_zero]))
  obtain ⟨a, ha⟩ := hKe (K.pOpcycles j x)
  refine ⟨a, (ModuleCat.mono_iff_injective (L.homologyι j)).mp inferInstance ?_⟩
  rw [show (ShortComplex.mk (homologyMap φ j) (homologyMap ψ j) hzero).f = homologyMap φ j from
    rfl, hιφ a, ha, opcyclesMap_pOpcycles_eq_of_add_d φ _ j rfl x z y hxz, hy]

/-- **In a degree with no outgoing differential, homology is opcycles**: if the map of opcycles
in degree `i` is an epimorphism, so is the map of homology. -/
theorem epi_homologyMap_of_epi_opcyclesMap (φ : K ⟶ L) (i j : ι) (hj : c.next i = j)
    (hK : K.d i j = 0) (hL : L.d i j = 0) (h : Epi (opcyclesMap φ i)) :
    Epi (homologyMap φ i) := by
  have h₁ := K.isIso_homologyι i j hj hK
  have h₂ := L.isIso_homologyι i j hj hL
  rw [show homologyMap φ i = K.homologyι i ≫ opcyclesMap φ i ≫ inv (L.homologyι i) by
    rw [← homologyι_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **The map of opcycles induced by a morphism of complexes of modules is an epimorphism as soon
as it is surjective on the cokernels of the differentials into that degree.** -/
theorem epi_opcyclesMap_of_surjective (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    (hsurj : ∀ y : L.X j, ∃ (x : K.X j) (z : L.X i), φ.f j x + L.d i j z = y) :
    Epi (opcyclesMap φ j) := by
  subst hi
  have hLp : Function.Surjective (L.pOpcycles j) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine (ModuleCat.epi_iff_surjective _).mpr fun b ↦ ?_
  obtain ⟨y, rfl⟩ := hLp b
  obtain ⟨x, z, hxz⟩ := hsurj y
  exact ⟨K.pOpcycles j x, opcyclesMap_pOpcycles_eq_of_add_d φ _ j rfl x z y hxz⟩

end HomologicalComplex

/-! ### Transport of the two conditions along additive identifications -/

namespace CochainComplex

variable {C₁ T₁ C₂ T₂ C₃ T₃ M₁ N₁ M₂ N₂ M₃ N₃ : Type*} [AddCommGroup C₁] [AddCommGroup T₁]
  [AddCommGroup C₂] [AddCommGroup T₂] [AddCommGroup C₃] [AddCommGroup T₃] [AddCommGroup M₁]
  [AddCommGroup N₁] [AddCommGroup M₂] [AddCommGroup N₂] [AddCommGroup M₃] [AddCommGroup N₃]
  {u₁ : C₁ ≃+ M₁} {u₀ : T₁ ≃+ N₁} {v₁ : C₂ ≃+ M₂} {v₀ : T₂ ≃+ N₂} {w₁ : C₃ ≃+ M₃}
  {w₀ : T₃ ≃+ N₃} {dK : C₁ → T₁} {dL : C₂ → T₂} {dM : C₃ → T₃} {pc : C₁ → C₂} {pt : T₁ → T₂}
  {rc : C₂ → C₃} {rt : T₂ → T₃} {d₁ : M₁ → N₁} {d₂ : M₂ → N₂} {d₃ : M₃ → N₃} {p : M₁ → M₂}
  {q : N₁ → N₂} {r : M₂ → M₃} {t : N₂ → N₃}

/-- The condition of `HomologicalComplex.exact_homologyMap_of_exists_cycle`, transported along
additive identifications of the degree `-1` and degree `0` terms of the three complexes. -/
theorem exists_cycle_of_addEquiv
    (hdK : ∀ z, u₀ (dK z) = d₁ (u₁ z)) (hdL : ∀ z, v₀ (dL z) = d₂ (v₁ z))
    (hp : ∀ z, v₁ (pc z) = p (u₁ z)) (hr : ∀ z, w₁ (rc z) = r (v₁ z))
    (h : ∀ m : M₂, d₂ m = 0 → r m = 0 → ∃ n : M₁, d₁ n = 0 ∧ p n = m)
    (m : C₂) (h1 : dL m = 0) (h2 : rc m = 0) : ∃ n : C₁, dK n = 0 ∧ pc n = m := by
  obtain ⟨n, hn₁, hn₂⟩ := h (v₁ m) (by rw [← hdL, h1, map_zero]) (by rw [← hr, h2, map_zero])
  refine ⟨u₁.symm n, u₀.injective ?_, v₁.injective ?_⟩
  · rw [hdK, u₁.apply_symm_apply, hn₁, map_zero]
  · rw [hp, u₁.apply_symm_apply, hn₂]

/-- The condition of `HomologicalComplex.exact_homologyMap_of_exists_add_d`, transported along
additive identifications of the degree `-1` and degree `0` terms of the three complexes. -/
theorem exists_add_d_of_addEquiv
    (hdL : ∀ z, v₀ (dL z) = d₂ (v₁ z)) (hdM : ∀ z, w₀ (dM z) = d₃ (w₁ z))
    (hq : ∀ z, v₀ (pt z) = q (u₀ z)) (ht : ∀ z, w₀ (rt z) = t (v₀ z))
    (h : ∀ n : N₂, (∃ m : M₃, d₃ m = t n) → ∃ (m : N₁) (z : M₂), q m + d₂ z = n)
    (n : T₂) (hn : ∃ m : C₃, dM m = rt n) : ∃ (m : T₁) (z : C₂), pt m + dL z = n := by
  obtain ⟨c, hc⟩ := hn
  obtain ⟨m, z, hmz⟩ := h (v₀ n) ⟨w₁ c, by rw [← hdM, hc, ht]⟩
  refine ⟨u₀.symm m, v₁.symm z, v₀.injective ?_⟩
  rw [map_add, hq, hdL, u₀.apply_symm_apply, v₁.apply_symm_apply, hmz]

end CochainComplex

end
