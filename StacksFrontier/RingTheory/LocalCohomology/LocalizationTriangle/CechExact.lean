module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechFunctor

/-!
# The extended alternating Čech complex is an exact functor of the module

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. Each term of the extended alternating Čech
complex `C^•(f₁, …, f_r; M)` is a finite direct sum of localizations of `M`, and localization of
modules is exact, so the whole complex is an exact functor of `M`: a short exact sequence of
`A`-modules induces a short exact sequence of Čech complexes.

## Main results

* `Stacks.LocalCohomology.cechModMap_add`, `Stacks.LocalCohomology.cechModMap_smul` — the map
  induced on a localization is additive and `A`-linear in the module map.
* `Stacks.LocalCohomology.cechTermMap_apply` — the induced map on a term of the complex acts
  componentwise.
* `Stacks.LocalCohomology.cechTermMap_injective`,
  `Stacks.LocalCohomology.cechTermMap_surjective`, `Stacks.LocalCohomology.cechTermMap_exact` —
  a short exact sequence of modules induces a short exact sequence of terms.
* `Stacks.LocalCohomology.shortExact_map_cechFunctor`,
  `Stacks.LocalCohomology.shortExact_map_extendedCechFunctor` — **the Čech complex is an exact
  functor of the module.**
* `Stacks.LocalCohomology.cechComplexMap_smul`,
  `Stacks.LocalCohomology.extendedCechComplexMap_smul` — the induced map of complexes is
  `A`-linear in the module map.
* `Stacks.LocalCohomology.extendMap_smul` — the extension of a morphism of `ℕ`-indexed complexes
  to `ℤ` is linear in the morphism.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  {M N P : ModuleCat.{max u v} R}

/-! ### A short complex all of whose objects vanish -/

/-- A short complex in which all three objects are zero objects is short exact. -/
theorem shortExact_of_isZero {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h₁ : IsZero S.X₁) (h₂ : IsZero S.X₂) (h₃ : IsZero S.X₃) : S.ShortExact where
  mono_f := ⟨fun _ _ _ ↦ h₁.eq_of_tgt _ _⟩
  epi_g := ⟨fun _ _ _ ↦ h₃.eq_of_src _ _⟩
  exact := S.exact_of_isZero_X₂ h₂

/-- A family of elements of the summands of a direct sum over a finite index type is the family
of components of an element of the direct sum. -/
theorem exists_directSum_of_components {ι : Type*} [Finite ι]
    (β : ι → Type*) [∀ i, AddCommGroup (β i)] [∀ i, Module R (β i)] (c : ∀ i, β i) :
    ∃ x : DirectSum ι β, ∀ s, x s = c s := by
  classical
  have := Fintype.ofFinite ι
  exact ⟨(DirectSum.linearEquivFunOnFintype R ι β).symm c, fun s ↦
    congrFun ((DirectSum.linearEquivFunOnFintype R ι β).apply_symm_apply c) s⟩

/-! ### Linearity of the map induced on a localization -/

/-- Two `R`-linear maps between localized Čech summands agree as soon as they agree after
composition with the localization map. -/
theorem cechMod_hom_ext {s : Finset (Fin r)}
    ⦃u v : Cech.cechMod f M s →ₗ[R] Cech.cechMod f N s⦄
    (h : u.comp (LocalizedModule.mkLinearMap (Cech.cechSub f s) M) =
      v.comp (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)) : u = v :=
  IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)
    (Cech.isUnit_algebraMap f N (le_refl s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) N)) h

/-- The map induced on a localization is additive in the module map. -/
theorem cechModMap_add (g h : M ⟶ N) (s : Finset (Fin r)) :
    cechModMap f (g + h) s = cechModMap f g s + cechModMap f h s :=
  cechMod_hom_ext f <| by
    ext m
    simp [cechModMap_mk]

/-- The map induced on a localization is `R`-linear in the module map. -/
theorem cechModMap_smul (a : R) (g : M ⟶ N) (s : Finset (Fin r)) :
    cechModMap f (a • g) s = a • cechModMap f g s :=
  cechMod_hom_ext f <| by
    ext m
    simp [cechModMap_mk]

/-- The zero module map induces the zero map on a localization. -/
@[simp] theorem cechModMap_zero (s : Finset (Fin r)) :
    cechModMap f (0 : M ⟶ N) s = 0 :=
  cechMod_hom_ext f <| by
    ext m
    simp

/-! ### Exactness of the map induced on a localization -/

/-- **Localization is exact**: an exact pair of module maps induces an exact pair on each
localized summand. -/
theorem cechModMap_exact (g : M ⟶ N) (h : N ⟶ P) (hex : Function.Exact g.hom h.hom)
    (s : Finset (Fin r)) :
    Function.Exact (cechModMap f g s) (cechModMap f h s) :=
  IsLocalizedModule.map_exact (Cech.cechSub f s) _ _ _ g.hom h.hom hex

/-- An injective module map induces an injective map on each localized summand. -/
theorem cechModMap_injective (g : M ⟶ N) (hg : Function.Injective g.hom)
    (s : Finset (Fin r)) : Function.Injective (cechModMap f g s) := by
  have := cechModMap_exact f (0 : M ⟶ M) g
    ((LinearMap.exact_zero_iff_injective _ _).2 hg) s
  rw [cechModMap_zero] at this
  exact (LinearMap.exact_zero_iff_injective _ _).1 this

/-- A surjective module map induces a surjective map on each localized summand. -/
theorem cechModMap_surjective (g : M ⟶ N) (hg : Function.Surjective g.hom)
    (s : Finset (Fin r)) : Function.Surjective (cechModMap f g s) := by
  have := cechModMap_exact f g (0 : N ⟶ N)
    ((LinearMap.exact_zero_iff_surjective _ _).2 hg) s
  rw [cechModMap_zero] at this
  exact (LinearMap.exact_zero_iff_surjective _ _).1 this

/-! ### The induced map on a term of the complex acts componentwise -/

/-- The map induced on the degree-`p` term of the Čech complex acts componentwise: its value at
the index `s` is the map induced on the localization at `s`. -/
theorem cechTermMap_apply (g : M ⟶ N) (p : ℕ) (x : Cech.cechTerm f M p)
    (s : {s : Finset (Fin r) // s.card = p}) :
    (cechTermMap f g p x) s = cechModMap f g s.1 (x s) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of t y =>
      rw [← DirectSum.lof_eq_of R, cechTermMap_lof, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
      rcases eq_or_ne t s with rfl | h
      · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne t s _ (Ne.symm h),
          DirectSum.of_eq_of_ne t s _ (Ne.symm h), map_zero]
  | add a b ha hb => simp [ha, hb]

/-- The induced map on a term of the complex is additive in the module map. -/
theorem cechTermMap_add (g h : M ⟶ N) (p : ℕ) :
    cechTermMap f (g + h) p = cechTermMap f g p + cechTermMap f h p :=
  LinearMap.ext fun x ↦ DirectSum.ext fun s ↦ by
    rw [cechTermMap_apply, cechModMap_add, LinearMap.add_apply, LinearMap.add_apply,
      DirectSum.add_apply, cechTermMap_apply, cechTermMap_apply]

/-- The induced map on a term of the complex is `R`-linear in the module map. -/
theorem cechTermMap_smul (a : R) (g : M ⟶ N) (p : ℕ) :
    cechTermMap f (a • g) p = a • cechTermMap f g p :=
  LinearMap.ext fun x ↦ DirectSum.ext fun s ↦ by
    rw [cechTermMap_apply, cechModMap_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      DirectSum.smul_apply, cechTermMap_apply]

/-! ### Exactness on the terms of the complex -/

/-- An element of a term of the Čech complex lies in the range of the induced map as soon as each
of its components lies in the range of the map induced on the corresponding localization. -/
theorem exists_cechTermMap_eq (g : M ⟶ N) (p : ℕ) (y : Cech.cechTerm f N p)
    (hy : ∀ s : {s : Finset (Fin r) // s.card = p}, ∃ z, cechModMap f g s.1 z = y s) :
    ∃ x, cechTermMap f g p x = y := by
  choose c hc using hy
  obtain ⟨x, hx⟩ := exists_directSum_of_components (R := R)
    (fun t : {s : Finset (Fin r) // s.card = p} ↦ Cech.cechMod f M t.1) c
  refine ⟨x, DirectSum.ext fun s ↦ ?_⟩
  rw [cechTermMap_apply, hx, hc]

/-- An injective module map induces an injective map on each term of the Čech complex. -/
theorem cechTermMap_injective (g : M ⟶ N) (hg : Function.Injective g.hom) (p : ℕ) :
    Function.Injective (cechTermMap f g p) := fun _ _ hxy ↦
  DirectSum.ext fun s ↦ cechModMap_injective f g hg s.1 <| by
    rw [← cechTermMap_apply, ← cechTermMap_apply, hxy]

/-- A surjective module map induces a surjective map on each term of the Čech complex. -/
theorem cechTermMap_surjective (g : M ⟶ N) (hg : Function.Surjective g.hom) (p : ℕ) :
    Function.Surjective (cechTermMap f g p) := fun y ↦
  exists_cechTermMap_eq f g p y fun s ↦ cechModMap_surjective f g hg s.1 (y s)

/-- **The terms of the Čech complex are exact functors of the module.** -/
theorem cechTermMap_exact (g : M ⟶ N) (h : N ⟶ P) (hex : Function.Exact g.hom h.hom) (p : ℕ) :
    Function.Exact (cechTermMap f g p) (cechTermMap f h p) := by
  intro y
  refine ⟨fun hy ↦ exists_cechTermMap_eq f g p y fun s ↦
    (cechModMap_exact f g h hex s.1 (y s)).1 ?_, ?_⟩
  · rw [← cechTermMap_apply, hy]
    simp
  · rintro ⟨x, rfl⟩
    refine DirectSum.ext fun s ↦ ?_
    rw [cechTermMap_apply, cechTermMap_apply, (cechModMap_exact f g h hex s.1 _).2 ⟨x s, rfl⟩]
    simp

/-- The extension of a morphism of `ℕ`-indexed complexes to `ℤ` is linear in the morphism. -/
theorem extendMap_smul {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [Linear R C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (a : R) (φ : K ⟶ L) (e : c.Embedding c') :
    HomologicalComplex.extendMap (a • φ) e = a • HomologicalComplex.extendMap φ e := by
  ext i'
  rcases Classical.em (∃ i, e.f i = i') with ⟨i, hi⟩ | hi'
  · simp [HomologicalComplex.extendMap_f _ e hi, HomologicalComplex.smul_f_apply]
  · exact (K.isZero_extend_X e i' (fun i hi ↦ hi' ⟨i, hi⟩)).eq_of_src _ _

/-! ### The Čech complex as an additive, linear, exact functor -/

/-- The induced map of `ℕ`-indexed Čech complexes is additive in the module map. -/
theorem cechComplexMap_add (g h : M ⟶ N) :
    cechComplexMap f (g + h) = cechComplexMap f g + cechComplexMap f h :=
  HomologicalComplex.hom_ext _ _ fun p ↦ by
    rw [cechComplexMap_f, cechTermMap_add, ModuleCat.ofHom_add, HomologicalComplex.add_f_apply,
      cechComplexMap_f, cechComplexMap_f]
    rfl

/-- The induced map of `ℕ`-indexed Čech complexes is `R`-linear in the module map. -/
theorem cechComplexMap_smul (a : R) (g : M ⟶ N) :
    cechComplexMap f (a • g) = a • cechComplexMap f g :=
  HomologicalComplex.hom_ext _ _ fun p ↦ by
    rw [cechComplexMap_f, cechTermMap_smul, HomologicalComplex.smul_f_apply, cechComplexMap_f]
    rfl

/-- The `ℕ`-indexed Čech complex is an additive functor of the module. -/
instance cechFunctor_additive (f : Fin r → R) : (cechFunctor.{v} f).Additive where
  map_add {_ _ g h} := cechComplexMap_add f g h

/-- The integer-indexed Čech map is the extension of the `ℕ`-indexed one. -/
theorem extendedCechComplexMap_eq_extendMap (g : M ⟶ N) :
    extendedCechComplexMap f g =
      HomologicalComplex.extendMap (cechComplexMap f g) ComplexShape.embeddingUpNat := rfl

/-- The induced map of `ℤ`-indexed Čech complexes is additive in the module map. -/
theorem extendedCechComplexMap_add (g h : M ⟶ N) :
    extendedCechComplexMap f (g + h) =
      extendedCechComplexMap f g + extendedCechComplexMap f h := by
  simp only [extendedCechComplexMap_eq_extendMap, cechComplexMap_add,
    HomologicalComplex.extendMap_add]

/-- The induced map of `ℤ`-indexed Čech complexes is `R`-linear in the module map. -/
theorem extendedCechComplexMap_smul (a : R) (g : M ⟶ N) :
    extendedCechComplexMap f (a • g) = a • extendedCechComplexMap f g := by
  simp only [extendedCechComplexMap_eq_extendMap, cechComplexMap_smul, extendMap_smul]

/-- The extended `ℤ`-indexed Čech complex is an additive functor of the module. -/
instance extendedCechFunctor_additive (f : Fin r → R) :
    (extendedCechFunctor.{v} f).Additive where
  map_add {_ _ g h} := extendedCechComplexMap_add f g h

/-- **A short exact sequence of modules induces a short exact sequence of `ℕ`-indexed Čech
complexes.** -/
theorem shortExact_map_cechFunctor (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) : (S.map (cechFunctor.{v} f)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦
    ModuleCat.shortComplex_shortExact _
      (cechTermMap_exact f S.f S.g
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact) p)
      (cechTermMap_injective f S.f hS.moduleCat_injective_f p)
      (cechTermMap_surjective f S.g hS.moduleCat_surjective_g p)

/-- The extension of an `ℕ`-indexed complex to `ℤ` preserves short exactness. -/
theorem shortExact_map_extendFunctor {C : Type*} [Category C] [Abelian C]
    (T : ShortComplex (CochainComplex C ℕ)) (hT : T.ShortExact) :
    (T.map (ComplexShape.embeddingUpNat.extendFunctor C)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ by
    rcases Int.lt_or_le i 0 with hi | hi
    · refine shortExact_of_isZero _ ?_ ?_ ?_ <;>
        exact HomologicalComplex.isZero_extend_X _ _ i
          (fun n ↦ by simp only [ComplexShape.embeddingUpNat_f]; omega)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
      exact (ShortComplex.shortExact_iff_of_iso
        (T.mapNatIso (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso C
          (i := n) (i' := (n : ℤ)) rfl))).2
        ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT n)

/-- **A short exact sequence of modules induces a short exact sequence of `ℤ`-indexed Čech
complexes**: the extended alternating Čech complex is an exact functor of the module. -/
theorem shortExact_map_extendedCechFunctor (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) : (S.map (extendedCechFunctor.{v} f)).ShortExact :=
  shortExact_map_extendFunctor _ (shortExact_map_cechFunctor.{v} f S hS)

end Stacks.LocalCohomology

end
