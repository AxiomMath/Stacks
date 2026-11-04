module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Kernel systems of an endomorphism and the cokernel tower

Let `A` be an abelian category, `M` an object of `A` and `f : M ⟶ M` an endomorphism. Write
`f^n` for the `n`-fold composite of `f`, `M[f^n]` for its kernel and `C_n = Coker(f^n)`.
Let `K_n` be the two-term complex `M --f^n--> M` (in degrees `-1, 0`) viewed in `D(A)`; the `K_n`
form an inverse system with transition maps `f` in degree `-1` and `id_M` in degree `0`, and the
`C_n` form an inverse system with the canonical epimorphisms `M / f^{n+1} M → M / f^n M`.
If the kernels `M[f^n]` stabilize, the two inverse systems are pro-isomorphic in `D(A)`.

## Main definitions

* `Ksys`: the inverse system `(K_n)` in `D(A)`.
* `Csys`: the inverse system `(C_n)` in `D(A)`.
* `Stabilizes`: there is `c ≥ 1` with `M[f^c] ≅ M[f^n]` via the inclusion for all `n ≥ c`.
* `Kproj`: the projection `K_n → H^0(K_n) = C_n`.
* `Cinv`: the map `C_{n+c} → K_n` obtained under stabilization.

## Main results

* `proIso_Ksys_Csys`: if `M[f^n]` stabilizes, `(K_n)` and `(C_n)` are pro-isomorphic in `D(A)`.

## Implementation notes

Inverse systems are functors `ℕᵒᵖ ⥤ D(A)` built with `Functor.ofOpSequence`, and they are
`0`-indexed: index `n : ℕ` corresponds to the exponent `n + 1`. The complex `K_n` is the mapping
cone of `f^{n+1}` between complexes concentrated in degree `0`; the sign of its differential does
not affect the object of `D(A)`. Pro-isomorphism is the explicit up-to-refinement form
`InverseSequence.ProIso`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type*} [Category C] [Abelian C]

namespace Stacks.InverseSystems.EndIterate

/-- `iterate f n = f^n : M ⟶ M`, the `n`-fold composite of `f` (with `iterate f 0 = id`). -/
def iterate {M : C} (f : M ⟶ M) : ℕ → (M ⟶ M)
  | 0 => 𝟙 M
  | (n + 1) => f ≫ iterate f n

omit [Abelian C] in
/-- `f^0 = id`. -/
@[simp] lemma iterate_zero {M : C} (f : M ⟶ M) : iterate f 0 = 𝟙 M := rfl

omit [Abelian C] in
/-- `f^{n+1} = f ≫ f^n`. -/
lemma iterate_succ {M : C} (f : M ⟶ M) (n : ℕ) : iterate f (n + 1) = f ≫ iterate f n := rfl

omit [Abelian C] in
/-- `f^{n+1} = f^n ≫ f`. -/
lemma iterate_succ' {M : C} (f : M ⟶ M) (n : ℕ) : iterate f (n + 1) = iterate f n ≫ f := by
  induction n with
  | zero => simp [iterate]
  | succ k ih => rw [iterate_succ, ih, ← Category.assoc, ← iterate_succ, ← ih]

omit [Abelian C] in
/-- `f^{m+n} = f^m ≫ f^n`. -/
lemma iterate_add {M : C} (f : M ⟶ M) (m n : ℕ) :
    iterate f (m + n) = iterate f m ≫ iterate f n := by
  induction n with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, iterate_succ', ih, iterate_succ', Category.assoc]

end Stacks.InverseSystems.EndIterate

open Stacks.InverseSystems.EndIterate

/-- The single-object functor `M ↦ (M placed in cohomological degree 0)`. -/
noncomputable abbrev sgl : C ⥤ CochainComplex C ℤ :=
  HomologicalComplex.single C (ComplexShape.up ℤ) 0

/-- The two-term complex `M --f^{n+1}--> M` (in cohomological degrees `-1, 0`), realised as the
mapping cone of `f^{n+1}` between complexes concentrated in degree `0`. -/
noncomputable def Kcx {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) : CochainComplex C
    ℤ :=
  CochainComplex.mappingCone (sgl.map (iterate f (n + 1)))

/-- The object `K_n` of `D(A)` represented by `Kcx f n`. -/
noncomputable def Kobj {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) : DerivedCategory C :=
  DerivedCategory.Q.obj (Kcx f n)

/-- The transition morphism `K_{n+1} → K_n`: `f` in degree `-1`, `id` in degree `0`. -/
noncomputable def Ktrans {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) :
    Kobj f (n + 1) ⟶ Kobj f n :=
  DerivedCategory.Q.map (CochainComplex.mappingCone.map
    (sgl.map (iterate f (n + 2))) (sgl.map (iterate f (n + 1)))
    (sgl.map f) (𝟙 _) (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_succ]))

/-- The first inverse system `(K_n)_{n ≥ 1}` as a functor `ℕᵒᵖ ⥤ D(A)`. -/
noncomputable def Ksys {M : C} (f : M ⟶ M) [HasDerivedCategory C] : ℕᵒᵖ ⥤ DerivedCategory C :=
  Functor.ofOpSequence (Ktrans f)

/-- `C_n = Coker(f^{n+1}) = M / f^{n+1} M` as an object of `D(A)` concentrated in degree `0`. -/
noncomputable def Cobj {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) : DerivedCategory C :=
  DerivedCategory.Q.obj (sgl.obj (cokernel (iterate f (n + 1))))

/-- The transition morphism `C_{n+1} → C_n`, the canonical epimorphism
`M / f^{n+2} M → M / f^{n+1} M`. -/
noncomputable def Ctrans {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) :
    Cobj f (n + 1) ⟶ Cobj f n :=
  DerivedCategory.Q.map (sgl.map
    (cokernel.map (iterate f (n + 2)) (iterate f (n + 1)) f (𝟙 M) (by
      rw [Category.comp_id, ← iterate_succ])))

/-- The second inverse system `(C_n)_{n ≥ 1}` as a functor `ℕᵒᵖ ⥤ D(A)`. -/
noncomputable def Csys {M : C} (f : M ⟶ M) [HasDerivedCategory C] : ℕᵒᵖ ⥤ DerivedCategory C :=
  Functor.ofOpSequence (Ctrans f)

/-- The canonical inclusion `M[f^c] ↪ M[f^n]` for `c ≤ n`, induced by `id_M`. -/
noncomputable def kerIncl {M : C} (f : M ⟶ M) {c n : ℕ} (h : c ≤ n) :
    kernel (iterate f c) ⟶ kernel (iterate f n) :=
  kernel.lift (iterate f n) (kernel.ι (iterate f c)) (by
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    rw [iterate_add, ← Category.assoc, kernel.condition, zero_comp])

/-- `M[f^n]` stabilizes: there is `c ≥ 1` such that for every `n ≥ c` the inclusion
`M[f^c] ↪ M[f^n]` is an isomorphism. -/
def Stabilizes {M : C} (f : M ⟶ M) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h)

/-- `Stabilizes f` holds iff some `c`, possibly `0`, has `M[f^c] ≅ M[f^n]` via the inclusion for
all `n ≥ c`: for `c = 0` every `M[f^n]` is isomorphic to `M[f^0] = 0`, and then `c = 1` works. -/
theorem stabilizes_iff_exists {M : C} (f : M ⟶ M) :
    Stabilizes f ↔ ∃ c : ℕ, ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h) := by
  refine ⟨fun ⟨c, _, h⟩ ↦ ⟨c, h⟩, fun ⟨c, h⟩ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have hz (m : ℕ) : IsZero (kernel (iterate f m)) :=
      (isZero_kernel_of_mono (𝟙 M)).of_iso (@asIso _ _ _ _ _ (h m m.zero_le)).symm
    exact ⟨1, le_rfl, fun n _ ↦ (hz 1).isIso (hz n) _⟩
  · exact ⟨c, hc, h⟩

/-- Under stabilization at `c`, the kernel of `f^n` for `n ≥ c` is killed by `f^c`. -/
private lemma kernel_ι_iterate_comp_iterate_eq_zero {M : C} (f : M ⟶ M) {c n : ℕ} (h : c ≤ n)
    (hi : IsIso (kerIncl f h)) : kernel.ι (iterate f n) ≫ iterate f c = 0 := by
  rw [← cancel_epi (kerIncl f h), comp_zero, kerIncl, kernel.lift_ι_assoc, kernel.condition]

/-- The successor transition map of `Functor.ofOpSequence g` is `g n`. -/
private lemma tr_ofOpSequence_le_succ {D : Type*} [Category D] {X : ℕ → D}
    (g : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) :
    InverseSequence.tr (Functor.ofOpSequence g) (Nat.le_succ n) = g n := by
  simp [InverseSequence.tr, Functor.ofOpSequence_map_homOfLE_succ]

/-- The projection `K_n → H^0(K_n) = C_n` in `D(A)`: the image under `Q` of the canonical map
`mappingCone (sgl.map f^{n+1}) → sgl(C_n)` of the cokernel short complex
`sgl(M) --sgl(f^{n+1})--> sgl(M) --→ sgl(coker f^{n+1})`. -/
noncomputable def Kproj {M : C} (f : M ⟶ M) [HasDerivedCategory C] (n : ℕ) :
    Kobj f n ⟶ Cobj f n :=
  DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
    (ShortComplex.mk (sgl.map (iterate f (n + 1)))
      (sgl.map (cokernel.π (iterate f (n + 1))))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])))

/-- `Kproj` is a morphism of inverse systems `(K_n) → (C_n)`. -/
theorem Kproj_naturality {M : C} (f : M ⟶ M) [HasDerivedCategory C] {m m' : ℕ} (h : m ≤ m') :
    InverseSequence.tr (Ksys f) h ≫ Kproj f m = Kproj f m' ≫ InverseSequence.tr (Csys f) h := by
  have succ (n : ℕ) : Ktrans f n ≫ Kproj f n = Kproj f (n + 1) ≫ Ctrans f n := by
    let S₂ : ShortComplex C := ShortComplex.mk (iterate f (n + 1))
      (cokernel.π (iterate f (n + 1))) (cokernel.condition _)
    let S₁ : ShortComplex C := ShortComplex.mk (iterate f (n + 2))
      (cokernel.π (iterate f (n + 2))) (cokernel.condition _)
    let φ : S₁ ⟶ S₂ := ShortComplex.Hom.mk f (𝟙 M)
      (cokernel.map (iterate f (n + 2)) (iterate f (n + 1)) f (𝟙 M)
        (by rw [Category.comp_id, ← iterate_succ]))
      (by dsimp [S₁, S₂]; rw [Category.comp_id, ← iterate_succ])
      (by dsimp [S₁, S₂]; rw [cokernel.π_desc])
    have nat := CochainComplex.mappingCone.descShortComplex_naturality (sgl.mapShortComplex.map φ)
    unfold Ktrans Kproj Ctrans
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    congr 1
    convert nat using 4
    all_goals first
      | exact (sgl.map_id M).symm
      | rfl
  have trK (n : ℕ) : InverseSequence.tr (Ksys f) (Nat.le_succ n) = Ktrans f n :=
    tr_ofOpSequence_le_succ _ n
  have trC (n : ℕ) : InverseSequence.tr (Csys f) (Nat.le_succ n) = Ctrans f n :=
    tr_ofOpSequence_le_succ _ n
  induction m', h using Nat.le_induction with
  | base =>
      rw [InverseSequence.ProIso.tr_refl, InverseSequence.ProIso.tr_refl, Category.id_comp]
      exact (Category.comp_id _).symm
  | succ k hk ih =>
      rw [← InverseSequence.ProIso.tr_trans (Ksys f) hk (Nat.le_succ k),
        ← InverseSequence.ProIso.tr_trans (Csys f) hk (Nat.le_succ k), trK, trC, Category.assoc,
        ih, ← Category.assoc, ← Category.assoc, succ k]

/-- The backward comparison map `C_{m+c} → K_m` in `D(A)`, for `c` at which `M[f^n]` stabilizes.
Since `M[f^{m+c+1}] = M[f^c]`, the map `f^{m+c+1}` factors as a monomorphism
`f̄ : M/M[f^c] → M`, so the two-term complex `M/M[f^c] --f̄--> M` is quasi-isomorphic to
`coker f̄ = C_{m+c}`; the square with vertical maps `M/M[f^c] → M` induced by `f^c` and `id_M`
gives a map from it to `K_m`. -/
noncomputable def Cinv {M : C} (f : M ⟶ M) [HasDerivedCategory C]
    (c : ℕ) (hstab : ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h)) (m : ℕ) :
    Cobj f (m + c) ⟶ Kobj f m := by
  let g := iterate f (m + c + 1)
  have hfac : Abelian.coimage.π g ≫ Abelian.factorThruCoimage g = g := Abelian.coimage.fac g
  have hzero : Abelian.factorThruCoimage g ≫ cokernel.π g = 0 := by
    rw [← cancel_epi (Abelian.coimage.π g), ← Category.assoc, hfac, cokernel.condition, comp_zero]
  let S : ShortComplex C := ShortComplex.mk (Abelian.factorThruCoimage g) (cokernel.π g) hzero
  have hcolim : IsColimit (CokernelCofork.ofπ S.g hzero) :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun {Z'} g' hg' => cokernel.desc g g' (by
        rw [← hfac, Category.assoc, hg', comp_zero]))
      (fun {Z'} g' hg' => cokernel.π_desc g g' _)
      (fun {Z'} g' hg' mm hm => by apply coequalizer.hom_ext; simpa using hm)
  have hexact : S.Exact := S.exact_of_g_is_cokernel hcolim
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk' hexact
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  let Ssgl : ShortComplex (CochainComplex C ℤ) := S.map sgl
  have hSEsgl : Ssgl.ShortExact := hSE.map_of_exact sgl
  let desc := CochainComplex.mappingCone.descShortComplex Ssgl
  have hqi : QuasiIso desc := CochainComplex.mappingCone.quasiIso_descShortComplex hSEsgl
  haveI hiso : IsIso (DerivedCategory.Q.map desc) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C desc).mpr hqi
  have hk : kernel.ι g ≫ iterate f c = 0 := by
    have hle : c ≤ m + c + 1 := by omega
    have hcomp : kerIncl f hle ≫ kernel.ι (iterate f (m + c + 1)) = kernel.ι (iterate f c) := by
      simp [kerIncl]
    have := hstab (m + c + 1) hle
    have hrw : kernel.ι (iterate f (m + c + 1))
        = inv (kerIncl f hle) ≫ kernel.ι (iterate f c) := by
      rw [← hcomp, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    change kernel.ι (iterate f (m + c + 1)) ≫ iterate f c = 0
    rw [hrw, Category.assoc, kernel.condition, comp_zero]
  let a₀ : Abelian.coimage g ⟶ M := cokernel.desc (kernel.ι g) (iterate f c) hk
  have hsq0 : Abelian.factorThruCoimage g = a₀ ≫ iterate f (m + 1) := by
    rw [← cancel_epi (Abelian.coimage.π g), hfac]
    change g = Abelian.coimage.π g ≫ a₀ ≫ iterate f (m + 1)
    rw [← Category.assoc]
    have hd : Abelian.coimage.π g ≫ a₀ = iterate f c :=
      cokernel.π_desc (kernel.ι g) (iterate f c) hk
    rw [hd, ← iterate_add]
    change iterate f (m + c + 1) = iterate f (c + (m + 1))
    congr 1; omega
  let cm := CochainComplex.mappingCone.map (sgl.map (Abelian.factorThruCoimage g))
    (sgl.map (iterate f (m + 1))) (sgl.map a₀) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp, ← hsq0])
  exact (inv (DerivedCategory.Q.map desc)) ≫ DerivedCategory.Q.map cm

/-- The coimage of `g` followed by `g`'s cokernel projection is zero. -/
private lemma factorThruCoimage_comp_cokernel_π {M : C} (g : M ⟶ M) :
    Abelian.factorThruCoimage g ≫ cokernel.π g = 0 := by
  rw [← cancel_epi (Abelian.coimage.π g), ← Category.assoc, Abelian.coimage.fac,
    cokernel.condition, comp_zero]

/-- The cone-to-cokernel map of `coimage g → M → coker g` becomes an isomorphism in `D(A)`. -/
private lemma isIso_Q_map_descShortComplex_coimage {M : C} [HasDerivedCategory C] (g : M ⟶ M) :
    IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
      ((ShortComplex.mk (Abelian.factorThruCoimage g) (cokernel.π g)
        (factorThruCoimage_comp_cokernel_π g)).map sgl))) := by
  have hcolim : IsColimit (CokernelCofork.ofπ (cokernel.π g)
      (factorThruCoimage_comp_cokernel_π g)) :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun {Z'} g' hg' => cokernel.desc g g' (by
        rw [← Abelian.coimage.fac g, Category.assoc, hg', comp_zero]))
      (fun {Z'} g' hg' => cokernel.π_desc g g' _)
      (fun {Z'} g' hg' mm hm => by apply coequalizer.hom_ext; simpa using hm)
  let S := ShortComplex.mk (Abelian.factorThruCoimage g) (cokernel.π g)
    (factorThruCoimage_comp_cokernel_π g)
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel hcolim)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso C _).mpr
    (CochainComplex.mappingCone.quasiIso_descShortComplex (hSE.map_of_exact sgl))

/-- If `a₀` extends `f^c` over the coimage of `f^{m+c+1}`, the coimage map is `a₀ ≫ f^{m+1}`. -/
private lemma factorThruCoimage_eq_comp_iterate {M : C} (f : M ⟶ M) (c m : ℕ)
    {a₀ : Abelian.coimage (iterate f (m + c + 1)) ⟶ M}
    (ha : Abelian.coimage.π (iterate f (m + c + 1)) ≫ a₀ = iterate f c) :
    Abelian.factorThruCoimage (iterate f (m + c + 1)) = a₀ ≫ iterate f (m + 1) := by
  rw [← cancel_epi (Abelian.coimage.π _), Abelian.coimage.fac, ← Category.assoc, ha,
    ← iterate_add]
  congr 1; omega

/-- `Cinv` is a morphism of inverse systems `(C_{m+c})_m → (K_m)_m`. -/
theorem Cinv_naturality {M : C} (f : M ⟶ M) [HasDerivedCategory C]
    (c : ℕ) (hstab : ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h)) {m m' : ℕ}
    (h : m ≤ m') :
    InverseSequence.tr (Csys f) (Nat.add_le_add_right h c) ≫ Cinv f c hstab m
      = Cinv f c hstab m' ≫ InverseSequence.tr (Ksys f) h := by
  set g : ℕ → (M ⟶ M) := fun m => iterate f (m + c + 1) with hg
  set S : ℕ → ShortComplex C := fun m => ShortComplex.mk (Abelian.factorThruCoimage (g m))
    (cokernel.π (g m)) (factorThruCoimage_comp_cokernel_π (g m)) with hS
  set Ssgl : ℕ → ShortComplex (CochainComplex C ℤ) := fun m => (S m).map sgl with hSsgl
  set descC : ∀ m, CochainComplex.mappingCone (Ssgl m).f ⟶ (Ssgl m).X₃ :=
    fun m => CochainComplex.mappingCone.descShortComplex (Ssgl m) with hdescC
  have hisoDesc : ∀ m, IsIso (DerivedCategory.Q.map (descC m)) :=
    fun m => isIso_Q_map_descShortComplex_coimage (g m)
  have hfac : ∀ m, Abelian.coimage.π (g m) ≫ Abelian.factorThruCoimage (g m) = g m :=
    fun m => Abelian.coimage.fac (g m)
  have hk (m : ℕ) : kernel.ι (g m) ≫ iterate f c = 0 :=
    kernel_ι_iterate_comp_iterate_eq_zero f _ (hstab (m + c + 1) (by omega))
  set a₀ : ∀ m, Abelian.coimage (g m) ⟶ M :=
    fun m => cokernel.desc (kernel.ι (g m)) (iterate f c) (hk m) with ha₀
  have hak (j : ℕ) : Abelian.coimage.π (g j) ≫ a₀ j = iterate f c := cokernel.π_desc _ _ _
  have hsq0 : ∀ m, Abelian.factorThruCoimage (g m) = a₀ m ≫ iterate f (m + 1) :=
    fun m => factorThruCoimage_eq_comp_iterate f c m (hak m)
  set cmC : ∀ m, CochainComplex.mappingCone (Ssgl m).f ⟶ Kcx f m :=
    fun m => CochainComplex.mappingCone.map (Ssgl m).f
      (sgl.map (iterate f (m + 1))) (sgl.map (a₀ m)) (𝟙 _) (by
        show (Ssgl m).f ≫ 𝟙 _ = sgl.map (a₀ m) ≫ sgl.map (iterate f (m + 1))
        rw [Category.comp_id, ← Functor.map_comp]
        show sgl.map (Abelian.factorThruCoimage (g m))
            = sgl.map (a₀ m ≫ iterate f (m + 1))
        rw [hsq0]) with hcmC
  have hCinv (m : ℕ) : Cinv f c hstab m
      = (inv (DerivedCategory.Q.map (descC m))) ≫ DerivedCategory.Q.map (cmC m) := rfl
  have hfgk : ∀ k, f ≫ g k = g (k+1) := by
    intro k; simp only [hg]; rw [← iterate_succ]; congr 1; omega
  have hkτ : ∀ k, kernel.ι (g (k+1)) ≫ (f ≫ Abelian.coimage.π (g k)) = 0 := by
    intro k
    have hfac2 : (kernel.ι (g (k+1)) ≫ f) ≫ g k = 0 := by
      rw [Category.assoc, hfgk, kernel.condition]
    have hw : kernel.ι (g (k+1)) ≫ f
        = kernel.lift (g k) (kernel.ι (g (k+1)) ≫ f) hfac2 ≫ kernel.ι (g k) := by
      rw [kernel.lift_ι]
    rw [← Category.assoc, hw, Category.assoc]
    show _ ≫ kernel.ι (g k) ≫ cokernel.π (kernel.ι (g k)) = 0
    rw [cokernel.condition, comp_zero]
  set τ₁ : ∀ k, Abelian.coimage (g (k+1)) ⟶ Abelian.coimage (g k) :=
    fun k => cokernel.desc (kernel.ι (g (k+1))) (f ≫ Abelian.coimage.π (g k)) (hkτ k) with hτ₁
  have hτ₁π (k : ℕ) : Abelian.coimage.π (g (k+1)) ≫ τ₁ k = f ≫ Abelian.coimage.π (g k) :=
    cokernel.π_desc _ _ _
  have hidA (k : ℕ) :
      Abelian.factorThruCoimage (g (k+1)) = τ₁ k ≫ Abelian.factorThruCoimage (g k) := by
    rw [← cancel_epi (Abelian.coimage.π (g (k+1))), hfac, ← Category.assoc, hτ₁π,
      Category.assoc, hfac, hfgk]
  have hidB (k : ℕ) : τ₁ k ≫ a₀ k = a₀ (k+1) ≫ f := by
    rw [← cancel_epi (Abelian.coimage.π (g (k+1))), ← Category.assoc, hτ₁π, Category.assoc, hak,
      ← Category.assoc, hak, ← iterate_succ, iterate_succ']
  have hcok0 : ∀ k, g (k+1) ≫ cokernel.π (g k) = 0 := by
    intro k; rw [← hfgk, Category.assoc, cokernel.condition, comp_zero]
  set τ₃ : ∀ k, cokernel (g (k+1)) ⟶ cokernel (g k) :=
    fun k => cokernel.desc (g (k+1)) (cokernel.π (g k)) (hcok0 k) with hτ₃
  set φ : ∀ k, S (k+1) ⟶ S k := fun k => ShortComplex.Hom.mk (τ₁ k) (𝟙 M) (τ₃ k)
    (by
      show τ₁ k ≫ Abelian.factorThruCoimage (g k) = Abelian.factorThruCoimage (g (k+1)) ≫ 𝟙 M
      rw [Category.comp_id]; exact (hidA k).symm)
    (by
      show 𝟙 M ≫ cokernel.π (g k) = cokernel.π (g (k+1)) ≫ τ₃ k
      rw [Category.id_comp]; exact (cokernel.π_desc _ _ _).symm) with hφ
  set dm : ∀ k,
      CochainComplex.mappingCone (Ssgl (k+1)).f ⟶ CochainComplex.mappingCone (Ssgl k).f :=
    fun k => CochainComplex.mappingCone.map (Ssgl (k+1)).f (Ssgl k).f
      (sgl.map (τ₁ k)) (sgl.map (𝟙 M))
      (by
        show sgl.map (Abelian.factorThruCoimage (g (k+1))) ≫ sgl.map (𝟙 M)
            = sgl.map (τ₁ k) ≫ sgl.map (Abelian.factorThruCoimage (g k))
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        rw [Category.comp_id]; exact hidA k) with hdm
  have hFact1 (k : ℕ) : dm k ≫ descC k = descC (k+1) ≫ sgl.map (τ₃ k) :=
    CochainComplex.mappingCone.descShortComplex_naturality (sgl.mapShortComplex.map (φ k))
  have hFact2 : ∀ k, cmC (k+1) ≫ CochainComplex.mappingCone.map
        (sgl.map (iterate f (k + 2))) (sgl.map (iterate f (k + 1)))
        (sgl.map f) (𝟙 _) (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_succ])
      = dm k ≫ cmC k := by
    intro k
    simp only [hcmC, hdm]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    congr 1
    · rw [← Functor.map_comp, ← Functor.map_comp]; congr 1; exact (hidB k).symm
    · rw [Category.comp_id, Category.comp_id]; exact (sgl.map_id M).symm
  have hsuccD : ∀ k, DerivedCategory.Q.map (sgl.map (τ₃ k)) ≫ Cinv f c hstab k
      = Cinv f c hstab (k+1) ≫ Ktrans f k := by
    intro k
    rw [hCinv, hCinv]
    have hKt : Ktrans f k = DerivedCategory.Q.map (CochainComplex.mappingCone.map
        (sgl.map (iterate f (k + 2))) (sgl.map (iterate f (k + 1)))
        (sgl.map f) (𝟙 _) (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_succ])) := rfl
    rw [hKt, Category.assoc, ← DerivedCategory.Q.map_comp, hFact2 k, DerivedCategory.Q.map_comp]
    have hF1Q : DerivedCategory.Q.map (dm k) ≫ DerivedCategory.Q.map (descC k)
        = DerivedCategory.Q.map (descC (k+1)) ≫ DerivedCategory.Q.map (sgl.map (τ₃ k)) := by
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hFact1 k]
    have hdmEq : DerivedCategory.Q.map (dm k)
        = DerivedCategory.Q.map (descC (k+1)) ≫ DerivedCategory.Q.map (sgl.map (τ₃ k))
          ≫ inv (DerivedCategory.Q.map (descC k)) := by
      rw [← Category.assoc, ← hF1Q, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hdmEq]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have htrC : ∀ k, InverseSequence.tr (Csys f) (show k + c ≤ (k + 1) + c by omega)
      = DerivedCategory.Q.map (sgl.map (τ₃ k)) := by
    intro k
    have hπ : cokernel.π (g (k + 1)) ≫ τ₃ k = cokernel.π (g k) := cokernel.π_desc _ _ _
    have eob : op ((k + 1) + c) = op ((k + c) + 1) := by
      rw [show (k + 1) + c = (k + c) + 1 by omega]
    have hsplit : (homOfLE (show k + c ≤ (k + 1) + c by omega)).op
        = eqToHom eob ≫ (homOfLE (Nat.le_succ (k + c))).op :=
      Subsingleton.elim _ _
    have hstep : InverseSequence.tr (Csys f) (show k + c ≤ (k + 1) + c by omega)
        = (Csys f).map (eqToHom eob) ≫ Ctrans f (k + c) := by
      rw [InverseSequence.tr, hsplit, Functor.map_comp]
      congr 1
      simp [Csys, Functor.ofOpSequence_map_homOfLE_succ]
    rw [hstep]
    have hco : cokernel (iterate f (k + c + 2)) = cokernel (g (k + 1)) := by
      rw [hg]; congr 2; omega
    have hcast : (Csys f).map (eqToHom eob)
        = DerivedCategory.Q.map (sgl.map (eqToHom hco.symm)) := by
      rw [eqToHom_map, eqToHom_map, eqToHom_map]
    rw [hcast, Ctrans, ← DerivedCategory.Q.map_comp, ← Functor.map_comp]
    congr 2
    apply (cancel_epi (cokernel.π (g (k + 1)))).1
    rw [hπ, ← Category.assoc]
    have hgg : g (k + 1) = iterate f (k + c + 2) := by
      rw [hg]; exact congrArg (iterate f) (by omega)
    have hπcast : cokernel.π (g (k + 1)) ≫ eqToHom hco.symm
        = cokernel.π (iterate f (k + c + 2)) := by
      have key : ∀ {a b : M ⟶ M} (hab : a = b) (he : cokernel a = cokernel b),
          cokernel.π a ≫ eqToHom he = cokernel.π b := by
        intro a b hab he
        subst hab
        rw [eqToHom_refl, Category.comp_id]
      exact key hgg hco.symm
    rw [hπcast, cokernel.π_desc, Category.id_comp]
  have trK (n : ℕ) : InverseSequence.tr (Ksys f) (Nat.le_succ n) = Ktrans f n :=
    tr_ofOpSequence_le_succ _ n
  induction m', h using Nat.le_induction with
  | base =>
      rw [InverseSequence.ProIso.tr_refl, InverseSequence.ProIso.tr_refl, Category.id_comp]
      exact (Category.comp_id _).symm
  | succ k hk ih =>
      rw [← InverseSequence.ProIso.tr_trans (Csys f) (Nat.add_le_add_right hk c)
          (show k + c ≤ (k + 1) + c by omega),
        ← InverseSequence.ProIso.tr_trans (Ksys f) hk (Nat.le_succ k), Category.assoc, ih htrC,
        ← Category.assoc, ← Category.assoc, htrC, trK, hsuccD]

/-- `Kproj` followed by `Cinv` is the transition map `K_{m+c} → K_m`. -/
theorem Cinv_Kproj {M : C} (f : M ⟶ M) [HasDerivedCategory C]
    (c : ℕ) (hstab : ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h)) (m : ℕ) :
    Kproj f (m + c) ≫ Cinv f c hstab m = InverseSequence.tr (Ksys f) (Nat.le_add_right m c) := by
  let g := iterate f (m + c + 1)
  have hfac : Abelian.coimage.π g ≫ Abelian.factorThruCoimage g = g := Abelian.coimage.fac g
  let S : ShortComplex C := ShortComplex.mk (Abelian.factorThruCoimage g) (cokernel.π g)
    (factorThruCoimage_comp_cokernel_π g)
  let Ssgl : ShortComplex (CochainComplex C ℤ) := S.map sgl
  let desc := CochainComplex.mappingCone.descShortComplex Ssgl
  have hiso : IsIso (DerivedCategory.Q.map desc) := isIso_Q_map_descShortComplex_coimage g
  have hk : kernel.ι g ≫ iterate f c = 0 :=
    kernel_ι_iterate_comp_iterate_eq_zero f _ (hstab (m + c + 1) (by omega))
  let a₀ : Abelian.coimage g ⟶ M := cokernel.desc (kernel.ι g) (iterate f c) hk
  have hπa₀ : Abelian.coimage.π g ≫ a₀ = iterate f c := cokernel.π_desc _ _ _
  have hsq0 : Abelian.factorThruCoimage g = a₀ ≫ iterate f (m + 1) :=
    factorThruCoimage_eq_comp_iterate f c m hπa₀
  let cm := CochainComplex.mappingCone.map (sgl.map (Abelian.factorThruCoimage g))
    (sgl.map (iterate f (m + 1))) (sgl.map a₀) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp, ← hsq0])
  have hCinv : Cinv f c hstab m
      = (inv (DerivedCategory.Q.map desc)) ≫ DerivedCategory.Q.map cm := rfl
  have hKzero : sgl.map (iterate f (m + c + 1)) ≫ sgl.map (cokernel.π (iterate f (m + c +
      1))) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  let SK : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk (sgl.map (iterate f (m + c + 1)))
      (sgl.map (cokernel.π (iterate f (m + c + 1)))) hKzero
  have hKproj : Kproj f (m + c)
      = DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex SK) := by
    show DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk (sgl.map (iterate f (m + c + 1)))
        (sgl.map (cokernel.π (iterate f (m + c + 1)))) _))
      = DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex SK)
    rfl
  let φ : SK ⟶ Ssgl := ShortComplex.Hom.mk (sgl.map (Abelian.coimage.π g)) (𝟙 _) (𝟙 _)
    (by
      show sgl.map (Abelian.coimage.π g) ≫ Ssgl.f
          = sgl.map (iterate f (m + c + 1)) ≫ 𝟙 _
      show sgl.map (Abelian.coimage.π g) ≫ sgl.map (Abelian.factorThruCoimage g)
          = sgl.map (iterate f (m + c + 1)) ≫ 𝟙 _
      rw [Category.comp_id, ← Functor.map_comp, hfac])
    (by
      show (𝟙 _ : sgl.obj M ⟶ sgl.obj M) ≫ Ssgl.g
          = sgl.map (cokernel.π (iterate f (m + c + 1))) ≫ 𝟙 _
      show (𝟙 _ : sgl.obj M ⟶ sgl.obj M) ≫ sgl.map (cokernel.π g)
          = sgl.map (cokernel.π (iterate f (m + c + 1))) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])
  let coimDesc := CochainComplex.mappingCone.map SK.f Ssgl.f φ.τ₁ φ.τ₂ (φ.comm₁₂).symm
  have hnat : coimDesc ≫ desc
      = CochainComplex.mappingCone.descShortComplex SK ≫ φ.τ₃ :=
    CochainComplex.mappingCone.descShortComplex_naturality φ
  have hnat' : coimDesc ≫ desc = CochainComplex.mappingCone.descShortComplex SK := by
    rw [hnat]; change _ ≫ 𝟙 _ = _; rw [Category.comp_id]
  rw [hKproj, hCinv, ← hnat', DerivedCategory.Q.map_comp, Category.assoc,
    IsIso.hom_inv_id_assoc, ← DerivedCategory.Q.map_comp]
  have hcomp : coimDesc ≫ cm
      = CochainComplex.mappingCone.map
          (sgl.map (iterate f (m + c + 1))) (sgl.map (iterate f (m + 1)))
          (sgl.map (iterate f c)) (𝟙 _)
          (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_add]; congr 2; omega) := by
    show CochainComplex.mappingCone.map (sgl.map (iterate f (m + c + 1)))
            (sgl.map (Abelian.factorThruCoimage g)) (sgl.map (Abelian.coimage.π g)) (𝟙 _) _
        ≫ CochainComplex.mappingCone.map (sgl.map (Abelian.factorThruCoimage g))
            (sgl.map (iterate f (m + 1))) (sgl.map a₀) (𝟙 _) _
        = _
    rw [← CochainComplex.mappingCone.map_comp]
    congr 1
    · rw [← Functor.map_comp, hπa₀]
    · rw [Category.comp_id]
  rw [hcomp]
  have key (j : ℕ) : InverseSequence.tr (Ksys f) (Nat.le_add_right m j)
      = DerivedCategory.Q.map (CochainComplex.mappingCone.map
          (sgl.map (iterate f (m + j + 1))) (sgl.map (iterate f (m + 1)))
          (sgl.map (iterate f j)) (𝟙 _)
          (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_add]; congr 2; omega)) := by
    induction j with
    | zero =>
        rw [InverseSequence.ProIso.tr_refl]
        have hmap : CochainComplex.mappingCone.map
            (sgl.map (iterate f (m + 0 + 1))) (sgl.map (iterate f (m + 1)))
            (sgl.map (iterate f 0)) (𝟙 _)
            (by rw [Category.comp_id, ← Functor.map_comp, ← iterate_add]; congr 2; omega)
            = 𝟙 (CochainComplex.mappingCone (sgl.map (iterate f (m + 0 + 1)))) := by
          convert CochainComplex.mappingCone.map_id (sgl.map (iterate f (m + 0 + 1))) using 2
          · rw [iterate_zero, sgl.map_id]
        rw [hmap, DerivedCategory.Q.map_id]
        rfl
    | succ k ih =>
        have hstep : InverseSequence.tr (Ksys f) (show m + k ≤ m + (k + 1) by omega)
            = Ktrans f (m + k) := tr_ofOpSequence_le_succ _ _
        rw [← InverseSequence.ProIso.tr_trans (Ksys f) (Nat.le_add_right m k)
            (show m + k ≤ m + (k + 1) by omega), ih, hstep, Ktrans, ← DerivedCategory.Q.map_comp]
        congr 1
        rw [← CochainComplex.mappingCone.map_comp]
        congr 1
        · rw [← Functor.map_comp]; rfl
        · rw [Category.comp_id]
  rw [key c]

/-- `Cinv` followed by `Kproj` is the transition map `C_{m+c} → C_m`. -/
theorem Kproj_Cinv {M : C} (f : M ⟶ M) [HasDerivedCategory C]
    (c : ℕ) (hstab : ∀ n, ∀ h : c ≤ n, IsIso (kerIncl f h)) (m : ℕ) :
    Cinv f c hstab m ≫ Kproj f m = InverseSequence.tr (Csys f) (Nat.le_add_right m c) := by
  let g := iterate f (m + c + 1)
  have hfac : Abelian.coimage.π g ≫ Abelian.factorThruCoimage g = g := Abelian.coimage.fac g
  let S : ShortComplex C := ShortComplex.mk (Abelian.factorThruCoimage g) (cokernel.π g)
    (factorThruCoimage_comp_cokernel_π g)
  let Ssgl : ShortComplex (CochainComplex C ℤ) := S.map sgl
  let desc := CochainComplex.mappingCone.descShortComplex Ssgl
  have hiso : IsIso (DerivedCategory.Q.map desc) := isIso_Q_map_descShortComplex_coimage g
  have hk : kernel.ι g ≫ iterate f c = 0 :=
    kernel_ι_iterate_comp_iterate_eq_zero f _ (hstab (m + c + 1) (by omega))
  let a₀ : Abelian.coimage g ⟶ M := cokernel.desc (kernel.ι g) (iterate f c) hk
  have hπa₀ : Abelian.coimage.π g ≫ a₀ = iterate f c := cokernel.π_desc _ _ _
  have hsq0 : Abelian.factorThruCoimage g = a₀ ≫ iterate f (m + 1) :=
    factorThruCoimage_eq_comp_iterate f c m hπa₀
  let cm := CochainComplex.mappingCone.map (sgl.map (Abelian.factorThruCoimage g))
    (sgl.map (iterate f (m + 1))) (sgl.map a₀) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp, ← hsq0])
  have hCinv : Cinv f c hstab m
      = (inv (DerivedCategory.Q.map desc)) ≫ DerivedCategory.Q.map cm := rfl
  have hKzero_m : sgl.map (iterate f (m + 1)) ≫ sgl.map (cokernel.π (iterate f (m + 1))) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  let SKm : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk (sgl.map (iterate f (m + 1)))
      (sgl.map (cokernel.π (iterate f (m + 1)))) hKzero_m
  have hKproj_m : Kproj f m
      = DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex SKm) := by
    show DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk (sgl.map (iterate f (m + 1)))
        (sgl.map (cokernel.π (iterate f (m + 1)))) _))
      = DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex SKm)
    rfl
  have hgfac : g = iterate f c ≫ iterate f (m + 1) := by
    show iterate f (m + c + 1) = iterate f c ≫ iterate f (m + 1)
    rw [← iterate_add]; congr 1; omega
  have hτ₃zero : g ≫ cokernel.π (iterate f (m + 1)) = 0 := by
    rw [hgfac, Category.assoc, cokernel.condition, comp_zero]
  let τ₃M : cokernel g ⟶ cokernel (iterate f (m + 1)) :=
    cokernel.desc g (cokernel.π (iterate f (m + 1))) hτ₃zero
  have hτ₃π : cokernel.π g ≫ τ₃M = cokernel.π (iterate f (m + 1)) :=
    cokernel.π_desc _ _ _
  let φ' : Ssgl ⟶ SKm := ShortComplex.Hom.mk (sgl.map a₀) (𝟙 _) (sgl.map τ₃M)
    (by
      show sgl.map a₀ ≫ SKm.f = Ssgl.f ≫ 𝟙 _
      show sgl.map a₀ ≫ sgl.map (iterate f (m + 1))
          = sgl.map (Abelian.factorThruCoimage g) ≫ 𝟙 _
      rw [Category.comp_id, ← Functor.map_comp, ← hsq0])
    (by
      show (𝟙 _ : sgl.obj M ⟶ sgl.obj M) ≫ SKm.g = Ssgl.g ≫ sgl.map τ₃M
      show (𝟙 _ : sgl.obj M ⟶ sgl.obj M) ≫ sgl.map (cokernel.π (iterate f (m + 1)))
          = sgl.map (cokernel.π g) ≫ sgl.map τ₃M
      rw [Category.id_comp, ← Functor.map_comp, hτ₃π])
  have hnat : CochainComplex.mappingCone.map Ssgl.f SKm.f φ'.τ₁ φ'.τ₂ (φ'.comm₁₂).symm
      ≫ CochainComplex.mappingCone.descShortComplex SKm
      = CochainComplex.mappingCone.descShortComplex Ssgl ≫ φ'.τ₃ :=
    CochainComplex.mappingCone.descShortComplex_naturality φ'
  have hcmeq : cm = CochainComplex.mappingCone.map Ssgl.f SKm.f φ'.τ₁ φ'.τ₂ (φ'.comm₁₂).symm := by
    rfl
  have hnat' : cm ≫ CochainComplex.mappingCone.descShortComplex SKm = desc ≫ sgl.map τ₃M := by
    rw [hcmeq, hnat]
  rw [hCinv, hKproj_m, Category.assoc, ← DerivedCategory.Q.map_comp, hnat',
    DerivedCategory.Q.map_comp, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have key (j : ℕ) (hz : iterate f (m + j + 1) ≫ cokernel.π (iterate f (m + 1)) = 0) :
      InverseSequence.tr (Csys f) (Nat.le_add_right m j)
      = DerivedCategory.Q.map (sgl.map
          (cokernel.desc (iterate f (m + j + 1)) (cokernel.π (iterate f (m + 1))) hz)) := by
    induction j with
    | zero =>
        rw [InverseSequence.ProIso.tr_refl]
        have hdescid : cokernel.desc (iterate f (m + 0 + 1)) (cokernel.π (iterate f (m + 1))) hz
            = 𝟙 (cokernel (iterate f (m + 0 + 1))) := by
          apply (cancel_epi (cokernel.π (iterate f (m + 0 + 1)))).1
          rw [cokernel.π_desc, Category.comp_id]
        rw [hdescid, sgl.map_id, DerivedCategory.Q.map_id]
        rfl
    | succ k ih =>
        have hstep : InverseSequence.tr (Csys f) (show m + k ≤ m + (k + 1) by omega)
            = Ctrans f (m + k) := tr_ofOpSequence_le_succ _ _
        have hz' : iterate f (m + k + 1) ≫ cokernel.π (iterate f (m + 1)) = 0 := by
          rw [show iterate f (m + k + 1) = iterate f k ≫ iterate f (m + 1) by
            rw [← iterate_add]; congr 1; omega, Category.assoc, cokernel.condition, comp_zero]
        rw [← InverseSequence.ProIso.tr_trans (Csys f) (Nat.le_add_right m k)
            (show m + k ≤ m + (k + 1) by omega), hstep, ih hz', Ctrans,
          ← DerivedCategory.Q.map_comp, ← Functor.map_comp]
        congr 2
        apply (cancel_epi (cokernel.π (iterate f (m + k + 2)))).1
        rw [← Category.assoc, cokernel.π_desc, Category.id_comp, cokernel.π_desc]
        show cokernel.π (iterate f (m + 1))
            = cokernel.π (iterate f (m + k + 2))
              ≫ cokernel.desc (iterate f (m + k + 2)) (cokernel.π (iterate f (m + 1))) hz
        rw [cokernel.π_desc]
  exact (key c hτ₃zero).symm

/-- If `M[f^n]` stabilizes, then the inverse systems `(K_n)` and `(C_n)` are pro-isomorphic in
`D(A)`. -/
@[stacks 0H3D]
theorem proIso_Ksys_Csys {M : C} (f : M ⟶ M) [HasDerivedCategory C] (hf : Stabilizes f) :
    Nonempty (InverseSequence.ProIso (Ksys f) (Csys f)) := by
  obtain ⟨c, _, hstab⟩ := hf
  exact ⟨{
    α := id
    β := fun m => m + c
    αmono := monotone_id
    βmono := fun a b h => by dsimp; omega
    αle := fun m => le_refl m
    βle := fun m => Nat.le_add_right m c
    φ := fun m => Kproj f m
    ψ := fun m => Cinv f c hstab m
    φnat := Kproj_naturality f
    ψnat := Cinv_naturality f c hstab
    ψφ := Cinv_Kproj f c hstab
    φψ := Kproj_Cinv f c hstab }⟩
