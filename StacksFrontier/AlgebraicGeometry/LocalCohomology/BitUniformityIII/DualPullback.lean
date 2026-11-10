module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.LinearAlgebra.Pi
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a module, its pullback, and the canonical comparison map

This file formalizes Stacks Project Tag 0GAB, the remark of the section *A bit of uniformity,
III* of the chapter *Local Cohomology* that introduces the duals used in Tag 0GAC.

## The statement of Tag 0GAB

Keep the situation of Tag 0GA6: a Noetherian ring `A`, an ideal `I ⊆ A`, the blowing up
`p : X → Spec(A)` of `Spec(A)` in `I`, and the thickenings `Yₙ` of the exceptional divisor, so
that `𝒪_{Yₙ} = p^*(A/Iⁿ)`. The remark does four things.

1. For a finite `A/Iⁿ`-module `M` it sets `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)`, and for a coherent
   `𝒪_{Yₙ}`-module `ℱ` it sets `ℱ^∨ = SheafHom_{𝒪_{Yₙ}}(ℱ, 𝒪_{Yₙ})`.
2. It produces a canonical map `can : p^*(M^∨) → (p^*M)^∨`, by choosing a presentation
   `(A/Iⁿ)^{⊕s} → (A/Iⁿ)^{⊕r} → M → 0`, dualizing both it and its pullback, and pulling the
   dualized presentation back.
3. It records that the construction is functorial in `M`.
4. It records that if `M` is an `(A, n, c)`-module then the kernel and cokernel of `can` are
   scheme theoretically supported on `Y_c`; the reason given is that for `a ∈ I^c` the map
   `a : M → M` factors through a finite free `A/Iⁿ`-module, for which `can` is an isomorphism,
   so that `a` annihilates the kernel and cokernel of `can`.

## What is formalized here, and where the rest is

The module-level dual of (1) is `Stacks.LocalCohomology.UniformityIII.moduleDual`, a functor
`(Mod(A/Iⁿ))ᵒᵖ ⥤ Mod(A/Iⁿ)`; no finiteness is needed to form it. The first step of the proof of
(4), that `a : M → M` factors through a finite free `A/Iⁿ`-module, is
`IsANCModule.exists_finFree_factorization`. Both carry the tag.

The sheaf-level dual of (1) is `Stacks.SheafOfModules.PullbackDual.dualModuleSheaf` of
`StacksFrontier.AlgebraicGeometry.Duality.PullbackOfDualSheaf`. The map `can` of (2), with the
source's source `p^*(M^∨) = f^*((M^∨)~)`, its functoriality (3), its invertibility at a finite
free module and the annihilation (4) are proved, for an arbitrary morphism of ringed sites
`f : X ⟶ Spec(A/Iⁿ)` in place of `p`, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackSource`, where they
carry the tag; there `can` is constructed, not assumed. The words "scheme theoretically
supported on `Y_c`" are the source's reading of (4) and are not formalized.

This file also carries, untagged, an abstract version of the argument:
`Stacks.LocalCohomology.UniformityIII.DualPullback` packages an additive functor
`pull : Mod(A/Iⁿ) ⥤ 𝒟` into a preadditive `A/Iⁿ`-linear category, an additive dual
`𝒟ᵒᵖ ⥤ 𝒟`, and a natural transformation

`can : (-)^∨ ⋙ pull ⟶ pull.op ⋙ (-)^∨`

invertible at the free module of rank one, and `DualPullback.smul_id_kernel_can_eq_zero` and
`DualPullback.smul_id_cokernel_can_eq_zero` prove (4) for such a datum. These assume `can` as a
field, so they are not tagged; `DualPullback.id` shows the hypotheses are consistent.

The diagram chase is isolated as `isIso_app_of_sum_id`, `kernel_ι_comp_map_eq_zero` and
`map_comp_cokernel_π_eq_zero`, statements about an arbitrary natural transformation; the
sheaf-level and the source-level forms of (4) both instantiate them.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.moduleDual`: the dual `M^∨ = Hom_R(M, R)` of a module,
  as a functor contravariant in `M`. This is the `M^∨` of the source.
* `Stacks.LocalCohomology.UniformityIII.finFreeModule`: the finite free module `R^{⊕r}`.
* `Stacks.LocalCohomology.UniformityIII.DualPullback`: the pullback functor and the canonical
  map `can` of the source, carried as data.
* `Stacks.LocalCohomology.UniformityIII.DualPullback.id`: the datum with `pull` the identity.

## Main results

* `Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_finFree_factorization`: for an
  `(A, n, c)`-module `M` and `a ∈ I^c` the map `a : M → M` factors through a finite free
  `A/Iⁿ`-module. This is the step the remark's proof of clause (4) opens with.
* `Stacks.LocalCohomology.UniformityIII.DualPullback.can_naturality`: clause (3), the
  functoriality of `can` in `M`.
* `Stacks.LocalCohomology.UniformityIII.DualPullback.isIso_can_finFree`: `can` is an
  isomorphism at a finite free module.
* `Stacks.LocalCohomology.UniformityIII.DualPullback.smul_id_kernel_can_eq_zero` and
  `Stacks.LocalCohomology.UniformityIII.DualPullback.smul_id_cokernel_can_eq_zero`: clause (4),
  that `I^c` annihilates the kernel and the cokernel of `can` at an `(A, n, c)`-module.

## Implementation notes

The linearity of `pull` and of the dual on `𝒟` is carried only in the one form the proof of
clause (4) uses — that a scalar multiple of an identity goes to the same scalar multiple of an
identity. The categorical `CategoryTheory.Linear` typeclass is not available on an opposite
category in Mathlib, so the dual's linearity cannot be stated as
`CategoryTheory.Functor.Linear`, and stating it for `pull` alone would be an asymmetry with no
gain.

The diagram chase behind clause (4) is isolated as
`Stacks.LocalCohomology.UniformityIII.kernel_ι_comp_map_eq_zero` and
`Stacks.LocalCohomology.UniformityIII.map_comp_cokernel_π_eq_zero`, statements about an
arbitrary natural transformation between functors into a category with kernels, respectively
cokernels: a morphism of the source category that factors through an object where the
transformation is invertible is killed by the kernel inclusion, respectively kills the cokernel
projection, of the transformation's component.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public section

universe u u₂ v₂ u₃ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.LocalCohomology.UniformityIII

/-! ## The dual of a module as a functor -/

section ModuleDual

variable (R : Type u) [CommRing R]

/-- The dual `M^∨ = Hom_R(M, R)` of an `R`-module, as a functor contravariant in `M`: on
morphisms it is `LinearMap.dualMap`, that is, precomposition. For `R = A/Iⁿ` this is the `M^∨`
of Tag 0GAB; no finiteness of `M` is needed to form it. -/
@[stacks 0GAB "the dual M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ) of a module over A/Iⁿ, and its functoriality",
  sga "3 VIIA 3.1.1" "affine dual object",
  sga "3 VIIA 4.3.3" "special case",
  sga "3 VIIB 1.3.5.C" "more general",
  sga "3 VIII 6.8"]
noncomputable def moduleDual : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Module.Dual R M.unop)
  map f := ModuleCat.ofHom (LinearMap.dualMap f.unop.hom)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- The dual functor `M ↦ M^∨` is additive. -/
instance : (moduleDual R).Additive where
  map_add {X Y} f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (φ : Module.Dual R X.unop) =>
      LinearMap.ext fun (m : Y.unop) => ?_)
    change φ ((f + g).unop.hom m) = φ (f.unop.hom m) + φ (g.unop.hom m)
    rw [show ((f + g).unop : Y.unop ⟶ X.unop) = f.unop + g.unop from rfl]
    simp

/-- Dualizing multiplication by `a` on `M` is multiplication by `a` on `M^∨`. -/
theorem moduleDual_map_op_smul_id (M : ModuleCat.{u} R) (a : R) :
    (moduleDual R).map (a • 𝟙 M).op = a • 𝟙 ((moduleDual R).obj (op M)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (φ : Module.Dual R M) =>
    LinearMap.ext fun (m : M) => ?_)
  change φ (a • m) = a • φ m
  exact map_smul φ a m

/-- The finite free module `R^{⊕r}`. -/
abbrev finFreeModule (r : ℕ) : ModuleCat.{u} R := ModuleCat.of R (Fin r → R)

/-- The `i`-th projection `R^{⊕r} ⟶ R`. -/
noncomputable abbrev finFreeProj (r : ℕ) (i : Fin r) :
    finFreeModule R r ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin r => R) i)

/-- The `i`-th inclusion `R ⟶ R^{⊕r}`. -/
noncomputable abbrev finFreeIncl (r : ℕ) (i : Fin r) :
    ModuleCat.of R R ⟶ finFreeModule R r :=
  ModuleCat.ofHom (LinearMap.single R (fun _ : Fin r => R) i)

/-- The identity of `R^{⊕r}` is the sum of the `r` maps `R^{⊕r} → R → R^{⊕r}`. -/
theorem sum_finFreeProj_comp_finFreeIncl (r : ℕ) :
    ∑ i : Fin r, finFreeProj R r i ≫ finFreeIncl R r i = 𝟙 (finFreeModule R r) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun j => ?_)
  rw [ModuleCat.hom_sum]
  simp [Pi.single_apply]

end ModuleDual

/-! ## The diagram chase -/

section Chase

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {S T : C ⥤ D} (can : S ⟶ T)

/-- **A natural transformation between additive functors which is invertible at `A` is
invertible at every object whose identity is a finite sum of maps through `A`.**

The inverse is assembled from the inverse at `A` by the same finite sum. This is what makes
the rank-one case of "`can` is an isomorphism at a finite free module" suffice. -/
theorem isIso_app_of_sum_id [Preadditive C] [S.Additive] [T.Additive] {A P : C}
    [IsIso (can.app A)] {ι : Type*} [Fintype ι] (p : ι → (P ⟶ A)) (q : ι → (A ⟶ P))
    (h : ∑ i, p i ≫ q i = 𝟙 P) : IsIso (can.app P) := by
  refine ⟨∑ i, T.map (p i) ≫ inv (can.app A) ≫ S.map (q i), ?_, ?_⟩
  · have key : ∀ i : ι, can.app P ≫ (T.map (p i) ≫ inv (can.app A) ≫ S.map (q i)) =
        S.map (p i ≫ q i) := fun i => by
      rw [S.map_comp, ← Category.assoc, ← can.naturality (p i)]
      simp
    rw [Preadditive.comp_sum, Finset.sum_congr rfl fun i _ => key i, ← S.map_sum, h,
      S.map_id]
  · have key : ∀ i : ι, (T.map (p i) ≫ inv (can.app A) ≫ S.map (q i)) ≫ can.app P =
        T.map (p i ≫ q i) := fun i => by
      rw [T.map_comp]
      simp only [Category.assoc, can.naturality (q i), IsIso.inv_hom_id_assoc]
    rw [Preadditive.sum_comp, Finset.sum_congr rfl fun i _ => key i, ← T.map_sum, h,
      T.map_id]

/-- **The kernel of `can` at `M` is killed by any endomorphism of `M` factoring through an
object at which `can` is invertible.** This is the kernel half of the diagram chase behind
clause (4) of Tag 0GAB. -/
theorem kernel_ι_comp_map_eq_zero [HasKernels D] {M F : C} (α : M ⟶ F) (β : F ⟶ M)
    [IsIso (can.app F)] : kernel.ι (can.app M) ≫ S.map (α ≫ β) = 0 := by
  have h : kernel.ι (can.app M) ≫ S.map α = 0 := by
    rw [← cancel_mono (can.app F), Category.assoc, can.naturality α, ← Category.assoc,
      kernel.condition, zero_comp, zero_comp]
  rw [S.map_comp, ← Category.assoc, h, zero_comp]

/-- **The cokernel of `can` at `M` is killed by any endomorphism of `M` factoring through an
object at which `can` is invertible.** This is the cokernel half of the diagram chase behind
clause (4) of Tag 0GAB. -/
theorem map_comp_cokernel_π_eq_zero [HasCokernels D] {M F : C} (α : M ⟶ F) (β : F ⟶ M)
    [IsIso (can.app F)] : T.map (α ≫ β) ≫ cokernel.π (can.app M) = 0 := by
  have h : T.map β ≫ cokernel.π (can.app M) = 0 := by
    rw [← cancel_epi (can.app F), ← Category.assoc, ← can.naturality β, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  rw [T.map_comp, Category.assoc, h, comp_zero]

variable {R : Type*} [CommRing R] [Linear R D]

/-- The kernel of `can` at `M` is annihilated by a scalar `a` as soon as `S` carries some
endomorphism of `M` factoring through an object at which `can` is invertible to `a` times the
identity. -/
theorem smul_id_kernel_eq_zero [HasKernels D] {M F : C} (α : M ⟶ F) (β : F ⟶ M)
    [IsIso (can.app F)] {a : R} (hS : S.map (α ≫ β) = a • 𝟙 (S.obj M)) :
    a • 𝟙 (kernel (can.app M)) = 0 := by
  have h := kernel_ι_comp_map_eq_zero can α β
  rw [hS, Linear.comp_smul, Category.comp_id] at h
  rw [← cancel_mono (kernel.ι (can.app M)), Linear.smul_comp, Category.id_comp, zero_comp]
  exact h

/-- The cokernel of `can` at `M` is annihilated by a scalar `a` as soon as `T` carries some
endomorphism of `M` factoring through an object at which `can` is invertible to `a` times the
identity. -/
theorem smul_id_cokernel_eq_zero [HasCokernels D] {M F : C} (α : M ⟶ F) (β : F ⟶ M)
    [IsIso (can.app F)] {a : R} (hT : T.map (α ≫ β) = a • 𝟙 (T.obj M)) :
    a • 𝟙 (cokernel (can.app M)) = 0 := by
  have h := map_comp_cokernel_π_eq_zero can α β
  rw [hT, Linear.smul_comp, Category.id_comp] at h
  rw [← cancel_epi (cokernel.π (can.app M)), Linear.comp_smul, Category.comp_id, comp_zero]
  exact h

end Chase

/-! ## The finite free factorization of an `(A, n, c)`-module -/

/-- **Stacks Project, Tag 0GAB.** For an `(A, n, c)`-module `M` and `a ∈ I^c` the
multiplication-by-`a` endomorphism of `M` factors through a *finite free* `A/Iⁿ`-module.

This is the step the remark's proof of clause (4) opens with. By `IsANCModule` the map factors
through a projective module; since `M` is finite it factors through a finite projective module
by Tag 0G91, and a finite projective module is a retract of a finite free one. -/
@[stacks 0GAB "for a ∈ I^c the map a : M → M factors through a finite free A/Iⁿ-module"]
theorem IsANCModule.exists_finFree_factorization {A : Type u} [CommRing A] {I : Ideal A}
    {n c : ℕ} {M : ModuleCat.{u} (A ⧸ I ^ n)} (hM : IsANCModule I n c M)
    {a : A ⧸ I ^ n} (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    ∃ (r : ℕ) (α : M ⟶ finFreeModule (A ⧸ I ^ n) r)
      (β : finFreeModule (A ⧸ I ^ n) r ⟶ M), α ≫ β = a • 𝟙 M := by
  have hfin : Module.Finite (A ⧸ I ^ n) M := hM.1
  obtain ⟨Q, _, _, _, _, α₀, β₀, hαβ⟩ :=
    Module.exists_finite_projective_factorization
      ((LinearMap.lsmul (A ⧸ I ^ n) (M : Type u)) a) (hM.2 a ha)
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) Q
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  refine ⟨r, ModuleCat.ofHom (s ∘ₗ α₀), ModuleCat.ofHom (β₀ ∘ₗ π), ?_⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change β₀ (π (s (α₀ m))) = (a • 𝟙 M).hom m
  change β₀ (π (s (α₀ m))) = a • m
  rw [show π (s (α₀ m)) = α₀ m from LinearMap.congr_fun hs (α₀ m)]
  exact (LinearMap.congr_fun hαβ m).symm

/-! ## The canonical map `can` and the annihilation of its kernel and cokernel -/

/-- **The data of Tag 0GAB.** A category `𝒟` of `𝒪_{Yₙ}`-modules, a pullback functor
`pull = p^*` from `A/Iⁿ`-modules to it, a dual on it, and the canonical map

`can : p^*(M^∨) ⟶ (p^*M)^∨`

of the source, carried as a natural transformation — so that its naturality square is the
functoriality in `M` that the source records. The only property of `can` carried is that it is
invertible at the free module of rank one; the source's "for which `can` is an isomorphism" at a
finite free module of arbitrary rank is deduced from it in `isIso_can_finFree`. -/
structure DualPullback (R : Type u) [CommRing R] (D : Type u₂) [Category.{v₂} D]
    [Preadditive D] [Linear R D] where
  /-- The pullback functor `p^*`. -/
  pull : ModuleCat.{u} R ⥤ D
  /-- `p^*` is additive. -/
  pull_additive : pull.Additive
  /-- The dual `ℱ ↦ ℱ^∨` on `𝒟`. -/
  dual : Dᵒᵖ ⥤ D
  /-- The dual is additive. -/
  dual_additive : dual.Additive
  /-- `p^*` is `R`-linear, in the one form the proof of clause (4) uses. -/
  pull_smul_id : ∀ (X : ModuleCat.{u} R) (b : R), pull.map (b • 𝟙 X) = b • 𝟙 (pull.obj X)
  /-- The dual is `R`-linear, in the one form the proof of clause (4) uses. -/
  dual_smul_id : ∀ (X : D) (b : R), dual.map (b • 𝟙 X).op = b • 𝟙 (dual.obj (op X))
  /-- The canonical map `can : p^*(M^∨) ⟶ (p^*M)^∨`. -/
  can : moduleDual R ⋙ pull ⟶ pull.op ⋙ dual
  /-- `can` is invertible at the free module of rank one. -/
  isIso_can_unit : IsIso (can.app (op (ModuleCat.of R R)))

attribute [instance] DualPullback.pull_additive DualPullback.dual_additive
  DualPullback.isIso_can_unit

namespace DualPullback

variable {R : Type u} [CommRing R] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [Linear R D] (P : DualPullback R D)

/-- The construction of `can` is functorial in the module `M`: for an `R`-linear map
`f : M ⟶ N` the square formed by `can` at `M` and at `N`, by the pullback of the dual of `f` and
by the dual of the pullback of `f`, commutes.

This is the clause of Tag 0GAB saying that the construction of `can` is functorial in `M`, but
it is *not* tagged: `can` is a field of `DualPullback`, so the statement assumes the very map
the remark constructs, and the naturality square is then true by the definition of a natural
transformation. The tag for that clause sits on
`Stacks.LocalCohomology.UniformityIII.pullbackModuleDualMap_naturality`, where `can` is built
and the square is proved. -/
theorem can_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    P.pull.map ((moduleDual R).map f.op) ≫ P.can.app (op M) =
      P.can.app (op N) ≫ P.dual.map (P.pull.map f).op :=
  P.can.naturality f.op

/-- `can` is an isomorphism at a finite free module. In the source this is the sentence "a
finite free `A/Iⁿ`-module for which `can` is an isomorphism"; here it is deduced from the
rank-one case, since the identity of `R^{⊕r}` is a finite sum of maps through `R`. -/
theorem isIso_can_finFree (r : ℕ) :
    IsIso (P.can.app (op (finFreeModule R r))) := by
  refine isIso_app_of_sum_id P.can (A := op (ModuleCat.of R R))
    (fun i => (finFreeIncl R r i).op) (fun i => (finFreeProj R r i).op) ?_
  rw [show (∑ i : Fin r, (finFreeIncl R r i).op ≫ (finFreeProj R r i).op) =
      ∑ i : Fin r, (finFreeProj R r i ≫ finFreeIncl R r i).op from rfl,
    ← op_sum, sum_finFreeProj_comp_finFreeIncl]
  rfl

/-- The source `p^*(M^∨)` of `can` carries multiplication by `a` on `M` to multiplication by
`a`. -/
theorem map_source_smul_id (M : ModuleCat.{u} R) (a : R) :
    (moduleDual R ⋙ P.pull).map (a • 𝟙 M).op =
      a • 𝟙 ((moduleDual R ⋙ P.pull).obj (op M)) := by
  change P.pull.map ((moduleDual R).map (a • 𝟙 M).op) = _
  rw [moduleDual_map_op_smul_id, P.pull_smul_id]
  rfl

/-- The target `(p^*M)^∨` of `can` carries multiplication by `a` on `M` to multiplication by
`a`. -/
theorem map_target_smul_id (M : ModuleCat.{u} R) (a : R) :
    (P.pull.op ⋙ P.dual).map (a • 𝟙 M).op =
      a • 𝟙 ((P.pull.op ⋙ P.dual).obj (op M)) := by
  change P.dual.map (P.pull.map (a • 𝟙 M)).op = _
  rw [P.pull_smul_id, P.dual_smul_id]
  rfl

end DualPullback

/-- For an `(A, n, c)`-module `M` and `a ∈ I^c`, multiplication by `a` on `M`, viewed in the
opposite category, factors through an object at which `can` is invertible. -/
private theorem DualPullback.exists_isIso_factorization {A : Type u} [CommRing A] {I : Ideal A}
    {n c : ℕ} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear (A ⧸ I ^ n) D]
    (P : DualPullback (A ⧸ I ^ n) D) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    ∃ (F : (ModuleCat.{u} (A ⧸ I ^ n))ᵒᵖ) (α : op M ⟶ F) (β : F ⟶ op M),
      IsIso (P.can.app F) ∧ α ≫ β = (a • 𝟙 M).op := by
  obtain ⟨r, α, β, hαβ⟩ := hM.exists_finFree_factorization ha
  exact ⟨_, β.op, α.op, P.isIso_can_finFree r, by rw [← hαβ]; rfl⟩

/-- If `M` is an `(A, n, c)`-module then, for the canonical map `can` of a `DualPullback`,
every `a ∈ I^c` annihilates the kernel of `can` at `M`.

This is the assertion of the remark's last clause: `a : M → M` factors through a finite free
`A/Iⁿ`-module, at which `can` is an isomorphism, and therefore `a` kills the kernel of `can`.
It is not tagged, for the reason given in the implementation notes: `can` is a field of
`DualPullback`, so the statement assumes the map Tag 0GAB constructs. -/
theorem DualPullback.smul_id_kernel_can_eq_zero {A : Type u} [CommRing A] {I : Ideal A}
    {n c : ℕ} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear (A ⧸ I ^ n) D]
    [HasKernels D] (P : DualPullback (A ⧸ I ^ n) D) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    a • 𝟙 (kernel (P.can.app (op M))) = 0 := by
  obtain ⟨F, α, β, _, h⟩ := P.exists_isIso_factorization hM ha
  refine smul_id_kernel_eq_zero P.can α β ?_
  rw [h]
  exact P.map_source_smul_id M a

/-- If `M` is an `(A, n, c)`-module then, for the canonical map `can` of a `DualPullback`,
every `a ∈ I^c` annihilates the cokernel of `can` at `M`. Untagged for the same reason as
`DualPullback.smul_id_kernel_can_eq_zero`. -/
theorem DualPullback.smul_id_cokernel_can_eq_zero {A : Type u} [CommRing A] {I : Ideal A}
    {n c : ℕ} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear (A ⧸ I ^ n) D]
    [HasCokernels D] (P : DualPullback (A ⧸ I ^ n) D) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    a • 𝟙 (cokernel (P.can.app (op M))) = 0 := by
  obtain ⟨F, α, β, _, h⟩ := P.exists_isIso_factorization hM ha
  refine smul_id_cokernel_eq_zero P.can α β ?_
  rw [h]
  exact P.map_target_smul_id M a

/-- The `DualPullback` with `pull` the identity functor of `Mod(R)` and `can` the identity: the
datum for a pullback along an isomorphism. It shows the hypotheses of `DualPullback` are
consistent. -/
noncomputable def DualPullback.id (R : Type u) [CommRing R] :
    DualPullback R (ModuleCat.{u} R) where
  pull := 𝟭 _
  pull_additive := inferInstance
  dual := moduleDual R
  dual_additive := inferInstance
  pull_smul_id _ _ := rfl
  dual_smul_id := moduleDual_map_op_smul_id R
  can := { app := fun _ => 𝟙 _, naturality := fun _ _ _ => by simp }
  isIso_can_unit := IsIso.id _

end Stacks.LocalCohomology.UniformityIII

end
