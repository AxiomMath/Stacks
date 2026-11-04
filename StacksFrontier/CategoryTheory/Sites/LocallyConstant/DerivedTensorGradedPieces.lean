module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.IdealPowerTriangles
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 094I: the graded pieces of the `I`-adic filtration

Let `(C, J)` be a site, let `Λ` be a Noetherian commutative ring and let `I ⊆ Λ` be an ideal.
Stacks Tag 094I asserts that for `K` in `D^-(C, Λ)` whose cohomology sheaves after reduction
modulo `I` are locally constant sheaves of finite type, the same holds after reduction modulo
`Iⁿ` for every `n ≥ 1`.

The source's proof is an induction on `n` along distinguished triangles
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`; that induction is
`isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_graded`, in the
namespace `Stacks.ConstantSheaf`, which takes the local constancy of the graded pieces
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` as a hypothesis. The source obtains that local constancy from the base change
identification `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ = (K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹` together with Tag 094H.

**This file proves it by a different route.** The module `Iⁿ/Iⁿ⁺¹` is a finitely generated
`Λ`-module killed by `I`; such a module is a quotient of a finite free `Λ/I`-module with kernel
again of that kind, so iterating the syzygy expresses
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹`, in any one degree, as built from finitely many copies of `K ⊗^L_Λ Λ/I`.
Neither a derived tensor product over `Λ/I` nor Tag 094H is needed.

## Main results

* `isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE`, in the
  namespace `Stacks.ConstantSheaf`:
  **Stacks Tag 094I**, for a derived tensor product supplied as a bifunctor `T`.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_of_annihilated`, in the
  same namespace:
  the step the source does by base change — the cohomology sheaves of `K ⊗^L_Λ M̲` are locally
  constant of finite type for every finitely generated `Λ`-module `M` killed by `I`.
* `Stacks.ConstantSheaf.exists_approx_derivedTensorConstant`: the iterated syzygy, as an
  approximation of `K ⊗^L_Λ M̲` accurate in degrees `> b - N`.
* `Stacks.ConstantSheaf.derivedCategoryB_derivedTensorConstant_finQuot`: the case of a finite
  free `Λ/I`-module.
* `Stacks.ConstantSheaf.exists_surjective_finQuot`: a finitely generated `Λ`-module killed by
  `I` is a quotient of some `(Λ/I)^a`.

## Implementation notes

**The derived tensor product enters as a bifunctor** `T` on `D(Sheaf J (ModuleCat Λ))`, and
`K ⊗^L_Λ M̲` is `Stacks.ConstantSheaf.derivedTensorConstant`: the construction
`Stacks.ConstantRingModules.constantDerivedTensor` needs the site small and every universe one,
while the statements here keep the module universe `max u v w` free. Two properties of `T` are
used, both of them properties of the derived tensor product of Tag 06YU: exactness in the second
variable, as the instances
`(T.obj K).CommShift ℤ` and `(T.obj K).IsTriangulated`, and the estimate
`K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b)`, as the hypothesis `hbound`. The
boundedness of `K` is the source's own `K ∈ D^-(C, Λ)`.

**Why the syzygy has to be iterated.** A single short exact sequence
`0 ⟶ Z ⟶ (Λ/I)^a ⟶ M ⟶ 0` relates `H^i(K ⊗^L_Λ M̲)` to `H^i` and `H^{i+1}` of `K ⊗^L_Λ Z̲` in
the same degrees, so by itself it gives nothing. What makes the argument terminate is that each
further syzygy shifts the error term one degree down while `K ⊗^L_Λ -` keeps it in degrees
`≤ b`: after `N` steps the error is in degrees `≤ b - N` and is invisible to `H^i` for
`i > b - N`. `Stacks.ConstantSheaf.exists_approx_derivedTensorConstant` carries exactly that --
an object with locally constant cohomology, a map to `K ⊗^L_Λ M̲`, and a bound on the error --
and the octahedral axiom is what advances it: applied to
`X_Z ⟶ K ⊗^L_Λ Z̲ ⟶ K ⊗^L_Λ (Λ/I)^a`, it produces the next approximation together with its
error term, which is the previous one shifted.

**Finite free modules are `Fin a → Λ/I`**, with their `Λ`-module structure; the rank is reduced
by the short exact sequence `Stacks.ConstantSheaf.finQuotShortComplex` rather than by a
decomposition into a biproduct, so no additivity of `T` beyond the triangulated structure is
invoked.

The module universe is `max u v w` and the coefficient ring is taken in `Type (max u v w)`.

## References

* [Stacks Project, Tag 094I](https://stacks.math.columbia.edu/tag/094I)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.ConstantSheaf

universe w v u s

/-! ### Finite free modules over `Λ/I` -/

section Algebra

variable (Λ : Type s) [CommRing Λ] (I : Ideal Λ)

/-- The inclusion of `Λ/I` as the zeroth coordinate of `Fin (a+1) → Λ/I`. -/
def finQuotIncl (a : ℕ) : (Λ ⧸ I) →ₗ[Λ] (Fin (a + 1) → (Λ ⧸ I)) :=
  LinearMap.single Λ (fun _ : Fin (a + 1) => (Λ ⧸ I)) 0

/-- The projection of `Fin (a+1) → Λ/I` onto the coordinates indexed by the successors. -/
def finQuotProj (a : ℕ) : (Fin (a + 1) → (Λ ⧸ I)) →ₗ[Λ] (Fin a → (Λ ⧸ I)) :=
  LinearMap.funLeft Λ (Λ ⧸ I) (Fin.succ : Fin a → Fin (a + 1))

/-- The zeroth coordinate is exactly the kernel of the projection onto the others. -/
theorem range_finQuotIncl_eq_ker_finQuotProj (a : ℕ) :
    LinearMap.range (finQuotIncl Λ I a) = LinearMap.ker (finQuotProj Λ I a) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine funext fun j => ?_
    simp [finQuotIncl, finQuotProj, LinearMap.funLeft, (Fin.succ_ne_zero j)]
  · intro y hy
    have hy' : ∀ j : Fin a, y j.succ = 0 := fun j => congrFun hy j
    refine ⟨y 0, funext fun i => ?_⟩
    induction i using Fin.cases with
    | zero => simp [finQuotIncl]
    | succ j =>
      simp only [finQuotIncl, LinearMap.coe_single, Pi.single_apply, hy' j]
      simp

/-- The inclusion of the zeroth coordinate is injective. -/
theorem injective_finQuotIncl (a : ℕ) : Function.Injective (finQuotIncl Λ I a) :=
  fun x y h => by simpa [finQuotIncl] using congrFun h 0

/-- **The short complex `Λ/I ⟶ (Fin (a+1) → Λ/I) ⟶ (Fin a → Λ/I)`** of `Λ`-modules which
exhibits a finite free `Λ/I`-module of rank `a + 1` as an extension of one of rank `a`. -/
def finQuotShortComplex (a : ℕ) : ShortComplex (ModuleCat.{s} Λ) where
  X₁ := ModuleCat.of Λ (Λ ⧸ I)
  X₂ := ModuleCat.of Λ (Fin (a + 1) → (Λ ⧸ I))
  X₃ := ModuleCat.of Λ (Fin a → (Λ ⧸ I))
  f := ModuleCat.ofHom (finQuotIncl Λ I a)
  g := ModuleCat.ofHom (finQuotProj Λ I a)
  zero := ModuleCat.hom_ext (LinearMap.ext fun x => by
    have hx : finQuotIncl Λ I a x ∈ LinearMap.ker (finQuotProj Λ I a) := by
      rw [← range_finQuotIncl_eq_ker_finQuotProj]
      exact ⟨x, rfl⟩
    simpa using hx)

/-- A short complex of `R`-modules with `range f = ker g`, `f` injective and `g` surjective is
short exact. -/
private theorem shortExact_of_range_eq_ker {R : Type s} [CommRing R]
    (S : ShortComplex (ModuleCat.{s} R)) (hfg : LinearMap.range S.f.hom = LinearMap.ker S.g.hom)
    (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rwa [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  · rwa [ModuleCat.mono_iff_injective]
  · rwa [ModuleCat.epi_iff_surjective]

/-- **The sequence `0 ⟶ Λ/I ⟶ (Fin (a+1) → Λ/I) ⟶ (Fin a → Λ/I) ⟶ 0` is short exact.** -/
theorem shortExact_finQuotShortComplex (a : ℕ) :
    (finQuotShortComplex Λ I a).ShortExact :=
  shortExact_of_range_eq_ker _ (range_finQuotIncl_eq_ker_finQuotProj Λ I a)
    (injective_finQuotIncl Λ I a)
    (LinearMap.funLeft_surjective_of_injective Λ (Λ ⧸ I) _ (Fin.succ_injective a))

/-- **A finitely generated `Λ`-module killed by `I` is a quotient of a finite free
`Λ/I`-module.** -/
theorem exists_surjective_finQuot (M : Type s) [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] (hM : ∀ r ∈ I, ∀ x : M, r • x = 0) :
    ∃ (a : ℕ) (π : (Fin a → (Λ ⧸ I)) →ₗ[Λ] M), Function.Surjective π := by
  obtain ⟨a, sgen, hsgen⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  have hker : ∀ i : Fin a, I ≤ LinearMap.ker (LinearMap.toSpanSingleton Λ M (sgen i)) :=
    fun i r hr => hM r hr (sgen i)
  refine ⟨a, ∑ i : Fin a, (Submodule.liftQ I _ (hker i)).comp (LinearMap.proj i), ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hsgen, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨(Pi.single i (1 : Λ ⧸ I) : Fin a → (Λ ⧸ I)), ?_⟩
  simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj]; simp)
    (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [Pi.single_eq_same]
  show Submodule.liftQ I _ (hker i) (Submodule.Quotient.mk (1 : Λ)) = sgen i
  rw [Submodule.liftQ_apply]
  simp [LinearMap.toSpanSingleton]

/-- **The short complex `ker π ⟶ (Fin a → Λ/I) ⟶ M`** attached to a map from a finite free
`Λ/I`-module to a `Λ`-module. -/
def kerShortComplex {a : ℕ} {M : ModuleCat.{s} Λ} (π : (Fin a → (Λ ⧸ I)) →ₗ[Λ] M) :
    ShortComplex (ModuleCat.{s} Λ) where
  X₁ := ModuleCat.of Λ (LinearMap.ker π)
  X₂ := ModuleCat.of Λ (Fin a → (Λ ⧸ I))
  X₃ := M
  f := ModuleCat.ofHom (LinearMap.ker π).subtype
  g := ModuleCat.ofHom π
  zero := ModuleCat.hom_ext (LinearMap.ext fun x => x.2)

/-- **The sequence `0 ⟶ ker π ⟶ (Fin a → Λ/I) ⟶ M ⟶ 0` is short exact** when `π` is
surjective. -/
theorem shortExact_kerShortComplex {a : ℕ} {M : ModuleCat.{s} Λ}
    (π : (Fin a → (Λ ⧸ I)) →ₗ[Λ] M) (hπ : Function.Surjective π) :
    (kerShortComplex Λ I π).ShortExact :=
  shortExact_of_range_eq_ker _ (Submodule.range_subtype _) Subtype.val_injective hπ

/-- **`Iⁿ/Iⁿ⁺¹` is killed by `I`**, since `I · Iⁿ ⊆ Iⁿ⁺¹`. -/
theorem smul_eq_zero_idealPowSuccQuot (n : ℕ) (r : Λ) (hr : r ∈ I)
    (x : idealPowSuccQuot Λ I n) : r • x = 0 := by
  revert x
  show ∀ x : ↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1)), r • x = 0
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show ((r • y : ↥(I ^ n)) : Λ) ∈ I ^ (n + 1)
  have hval : ((r • y : ↥(I ^ n)) : Λ) = (y : Λ) * r := by
    simp [mul_comm]
  rw [pow_succ, hval]
  exact Ideal.mul_mem_mul y.2 hr

end Algebra

/-! ### Degreewise comparison along a distinguished triangle -/

section Comparison

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

end Comparison

/-! ### The derived tensor product with a finite module killed by `I` -/

section Sheaves

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v w)) [CommRing Λ]

attribute [local instance] HasDerivedCategory.standard

/-- **The triangle of a short exact sequence of `Λ`-modules tensored with `K`.** For a bifunctor
`T` exact in its second variable, a short exact sequence of `Λ`-modules becomes, after passing
to constant sheaves in degree zero and tensoring with `K`, a distinguished triangle. -/
theorem exists_distTriang_derivedTensorConstant_of_shortExact
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (S : ShortComplex (ModuleCat.{max u v w} Λ)) (hS : S.ShortExact) :
    ∃ (f : derivedTensorConstant J Λ T K S.X₁ ⟶ derivedTensorConstant J Λ T K S.X₂)
      (g : derivedTensorConstant J Λ T K S.X₂ ⟶ derivedTensorConstant J Λ T K S.X₃)
      (h : derivedTensorConstant J Λ T K S.X₃ ⟶
        (derivedTensorConstant J Λ T K S.X₁)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) :=
  exists_distTriang_map_singleTriangle (T.obj K)
    (S.map (constantSheaf J (ModuleCat.{max u v w} Λ)))
    (shortExact_map_constantSheaf J Λ S hS)

/-- **`K ⊗^L_Λ M̲` is in degrees `≤ b` when `K` is**, since `M̲` sits in degree zero. -/
theorem isLE_derivedTensorConstant
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (hbound : ∀ (K L : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (a b : ℤ),
      K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b))
    (b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) [K.IsLE b]
    (M : ModuleCat.{max u v w} Λ) :
    (derivedTensorConstant J Λ T K M).IsLE b := by
  have h0 : ((derivedConstantSheaf J Λ).obj M).IsLE 0 := by
    show ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) 0).obj
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M)).IsLE 0
    infer_instance
  have h := hbound K ((derivedConstantSheaf J Λ).obj M) b 0 inferInstance h0
  rw [add_zero] at h
  exact h

section Noetherian

variable [IsNoetherianRing Λ] (I : Ideal Λ)

/-- **`K ⊗^L_Λ (Λ/I)^a` has locally constant cohomology sheaves of finite type.** By induction
on `a` along the short exact sequences
`0 ⟶ Λ/I ⟶ (Λ/I)^{a+1} ⟶ (Λ/I)^a ⟶ 0`, whose triangles the locally constant sheaves of finite
type absorb, being a weak Serre subcategory. -/
theorem derivedCategoryB_derivedTensorConstant_finQuot
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (a : ℕ) :
    DerivedCategoryB.derivedCategoryB (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ)
      (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Fin a → (Λ ⧸ I)))) := by
  have hserre : WeakSerre.IsWeakSerre (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  induction a with
  | zero =>
    have hz : IsZero (ModuleCat.of Λ (Fin 0 → (Λ ⧸ I))) :=
      ModuleCat.isZero_of_subsingleton _
    have hzero : IsZero (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Fin 0 → (Λ ⧸ I)))) := by
      refine Functor.map_isZero (T.obj K) ?_
      show IsZero ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) 0).obj
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj (ModuleCat.of Λ (Fin 0 → (Λ ⧸ I)))))
      exact Functor.map_isZero _ (Functor.map_isZero _ hz)
    exact fun n => DerivedCategoryB.zero_mem_of_isWeakSerre _ hserre _
      (Functor.map_isZero _ hzero)
  | succ a iha =>
    obtain ⟨f, g, h, hdist⟩ := exists_distTriang_derivedTensorConstant_of_shortExact J Λ T K
      (finQuotShortComplex Λ I a) (shortExact_finQuotShortComplex Λ I a)
    exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _ hserre
      (Triangle.mk f g h) hdist hbase iha

/-- **The `N`-th approximation of `K ⊗^L_Λ M̲`.** Let `M` be a finitely generated `Λ`-module
killed by `I`. There is an object `X` with locally constant cohomology sheaves of finite type
and a distinguished triangle `C ⟶ X ⟶ K ⊗^L_Λ M̲ ⟶ C[1]` whose remaining vertex `C` lies in
degrees `≤ b - N`; so `X` computes the cohomology sheaves of `K ⊗^L_Λ M̲` in degrees `> b - N`.

The induction on `N` is the iterated syzygy: a finite free `Λ/I`-module `F` surjects
onto `M` with kernel `Z` again finitely generated and killed by `I`, and the octahedral axiom
applied to `X_Z ⟶ K ⊗^L_Λ Z̲ ⟶ K ⊗^L_Λ F̲` turns the `N`-th approximation of `K ⊗^L_Λ Z̲` into
the `(N+1)`-st of `K ⊗^L_Λ M̲`, the error term acquiring one shift at each step. -/
theorem exists_approx_derivedTensorConstant
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (hbound : ∀ (K L : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (a b : ℤ),
      K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b))
    (b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) [K.IsLE b]
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (N : ℕ) :
    ∀ M : ModuleCat.{max u v w} Λ, ModuleCat.isFG Λ M →
      (∀ r ∈ I, ∀ x : M, r • x = 0) →
      ∃ (X Cerr : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
        (f : Cerr ⟶ X) (g : X ⟶ derivedTensorConstant J Λ T K M)
        (h : derivedTensorConstant J Λ T K M ⟶ Cerr⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang (DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) ∧
          DerivedCategoryB.derivedCategoryB
            (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) X ∧
          Cerr.IsLE (b - N) := by
  have hserre : WeakSerre.IsWeakSerre (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  induction N with
  | zero =>
    intro M hM hkill
    have : Module.Finite Λ M := (ModuleCat.isFG_iff M).mp hM
    obtain ⟨a, π, hπ⟩ := exists_surjective_finQuot Λ I M hkill
    obtain ⟨f, g, h, hdist⟩ := exists_distTriang_derivedTensorConstant_of_shortExact J Λ T K
      (kerShortComplex Λ I π) (shortExact_kerShortComplex Λ I π hπ)
    refine ⟨_, _, f, g, h, hdist,
      derivedCategoryB_derivedTensorConstant_finQuot J Λ I T K hbase a, ?_⟩
    simpa using isLE_derivedTensorConstant J Λ T hbound b K (kerShortComplex Λ I π).X₁
  | succ N ih =>
    intro M hM hkill
    have : Module.Finite Λ M := (ModuleCat.isFG_iff M).mp hM
    obtain ⟨a, π, hπ⟩ := exists_surjective_finQuot Λ I M hkill
    -- the syzygy `Z = ker π`
    have hZfg : ModuleCat.isFG Λ (kerShortComplex Λ I π).X₁ := by
      rw [ModuleCat.isFG_iff]
      have : IsNoetherian Λ (Fin a → (Λ ⧸ I)) := inferInstance
      exact Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker π))
    have hambient : ∀ r ∈ I, ∀ y : Fin a → (Λ ⧸ I), r • y = 0 := by
      intro r hr y
      refine funext fun j => ?_
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective I (y j)
      show r • y j = 0
      rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right c I hr
    have hZkill : ∀ r ∈ I, ∀ x : (kerShortComplex Λ I π).X₁, r • x = 0 := by
      show ∀ r ∈ I, ∀ x : ModuleCat.of Λ (LinearMap.ker π), r • x = 0
      exact fun r hr x => Subtype.ext (hambient r hr x.1)
    obtain ⟨XZ, CZ, fZ, gZ, hZ, hdistZ, hXZ, hCZ⟩ := ih _ hZfg hZkill
    obtain ⟨v, wmap, δ, hdistSES⟩ := exists_distTriang_derivedTensorConstant_of_shortExact
      J Λ T K (kerShortComplex Λ I π) (shortExact_kerShortComplex Λ I π hπ)
    obtain ⟨XM, v₁₃, w₁₃, hdist₁₃⟩ := distinguished_cocone_triangle (gZ ≫ v)
    have oct := Triangulated.someOctahedron (rfl : gZ ≫ v = gZ ≫ v)
      (rot_of_distTriang _ hdistZ) hdistSES hdist₁₃
    refine ⟨XM, CZ⟦(1 : ℤ)⟧, oct.m₁, oct.m₃, _, oct.mem, ?_, ?_⟩
    · exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _ hserre
        (Triangle.mk v₁₃ w₁₃ (-((gZ ≫ v)⟦(1 : ℤ)⟧'))) (rot_of_distTriang _ hdist₁₃)
        (derivedCategoryB_derivedTensorConstant_finQuot J Λ I T K hbase a)
        (DerivedCategoryB.derivedCategoryB_shift_mem _ hserre 1 hXZ)
    · exact DerivedCategory.TStructure.t.isLE_shift CZ (b - N) 1 (b - (N + 1 : ℕ))
        (by push_cast; ring)

/-- **The cohomology sheaves of `K ⊗^L_Λ M̲` are locally constant of finite type** for every
finitely generated `Λ`-module `M` killed by `I`, as soon as those of `K ⊗^L_Λ (Λ/I)̲` are.

This is the source's base change step, in the only form Tag 094I uses it: a finite free
`Λ/I`-resolution of `M` lets `K ⊗^L_Λ M̲` be computed, in any fixed degree, by a finite
extension of copies of `K ⊗^L_Λ (Λ/I)̲`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_of_annihilated
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (hbound : ∀ (K L : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (a b : ℤ),
      K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b))
    (b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) [K.IsLE b]
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (M : ModuleCat.{max u v w} Λ) (hM : ModuleCat.isFG Λ M)
    (hkill : ∀ r ∈ I, ∀ x : M, r • x = 0) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj (derivedTensorConstant J Λ T K M)) := by
  have hserre : WeakSerre.IsWeakSerre (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  obtain ⟨X, Cerr, f, g, h, hdist, hX, hCerr⟩ :=
    exists_approx_derivedTensorConstant J Λ I T hbound b K hbase ((b - i).toNat + 1) M hM hkill
  have hlt : b - ((b - i).toNat + 1 : ℕ) < i := by
    have := Int.self_le_toNat (b - i)
    push_cast
    omega
  have hiso := isIso_homologyMap_mor₂_of_isLE hdist (b - ((b - i).toNat + 1 : ℕ)) i hCerr hlt
  exact hserre.isClosedUnderIsomorphisms.of_iso
    (asIso ((DerivedCategory.homologyFunctor _ i).map (Triangle.mk f g h).mor₂)) (hX i)

/-! ### Tag 094I -/

/-- **Stacks Tag 094I.** Let `(C, J)` be a site, let `Λ` be a Noetherian ring, let `I ⊆ Λ` be an
ideal and let `K` be an object of `D^-` of the sheaves of `Λ`-modules. Let `T` stand for the
derived tensor product over `Λ`: a bifunctor on that derived category which is exact in its
second variable and carries objects in degrees `≤ a` and `≤ b` to objects in degrees `≤ a + b`.
If the cohomology sheaves of `K ⊗^L_Λ Λ/I` are locally constant of finite type, then so are
those of `K ⊗^L_Λ Λ/Iⁿ` for every `n ≥ 1`.

For the **constructed** derived tensor product `Stacks.ConstantSheaf.constantDerivedTensor` —
Tag 06YU for the constant ringed site, read through the equivalence of Tag 03ET — the bifunctor
`T`, its two exactness instances and `hbound` are discharged in
`isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_quotientIdealPow`, which
applies this theorem; the generality `Λ : Type (max u v w)` here is one the construction cannot
be given.

The proof is the source's induction on `n` along the distinguished triangles

`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`,

supplied by `Stacks.ConstantSheaf.exists_distTriang_derivedTensorConstant`, with the locally
constant sheaves of finite type absorbing the middle vertex because they form a weak Serre
subcategory (Tag 093U, through Tag 06UQ). Its remaining input, the local constancy of the graded
pieces `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹`, is
`isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_of_annihilated`:
`Iⁿ/Iⁿ⁺¹` is a finitely generated `Λ`-module killed by `I`, hence has a resolution by finite
free `Λ/I`-modules, which computes each cohomology sheaf of `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` out of finitely
many copies of `K ⊗^L_Λ Λ/I`. That replaces the source's base change identification
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ = (K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹` together with Tag 094H, and needs neither a
derived tensor product over `Λ/I` nor Tag 094H.

**The conclusion is stated over `Λ`, not over `Λ/Iⁿ`**: a `Λ`-module killed by `Iⁿ` is of
finite type over `Λ` exactly when it is over `Λ/Iⁿ`
(`Stacks.ConstantSheaf.module_finite_iff_finite_quotient`), and constant for one ring exactly
when constant for the other.

Besides the source's own hypotheses — `Λ` Noetherian, `I ⊆ Λ` an ideal, `K` in `D^-`, and the
local constancy of `K ⊗^L_Λ Λ/I` — the binders hold only the bifunctor `T` with the two
properties of a derived tensor product that the argument consumes: exactness in the second
variable, and the bound above. -/
@[stacks 094I "the induction on n from Λ/I to Λ/Iⁿ, with the source's distinguished triangles \
  and its base change to Λ/I both proved rather than assumed. The derived tensor product enters \
  as a bifunctor parameter, and two of its properties are hypotheses: exactness in the second \
  variable, and that it takes objects in degrees ≤ a and ≤ b to objects in degrees ≤ a + b. The \
  parameter is instantiated, and this tag registered with nothing assumed of the derived tensor \
  product, on Stacks.ConstantRingModules.\
isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_quotientIdealPow"]
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (hbound : ∀ (K L : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (a b : ℤ),
      K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b))
    (b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) [K.IsLE b]
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)))) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_graded J Λ T K I
    (fun m _ => isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_of_annihilated
      J Λ I T hbound b K hbase (idealPowSuccQuot Λ I m) (isFG_idealPowSuccQuot Λ I m)
      (fun r hr => smul_eq_zero_idealPowSuccQuot Λ I m r hr))
    hbase n hn

end Noetherian

end Sheaves

end Stacks.ConstantSheaf

end
