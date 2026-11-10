module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.Algebra.Module.Pure.Injective
public import StacksFrontier.Homology.TorAmplitude.Termwise

/-!
# Pure projective resolutions

A *pure projective resolution* of a module is a chain complex of pure projective modules,
universally exact and augmented over the module.  This file shows a module map extends to a
comparison map from a pure projective resolution to any universally exact resolution, and that
two such comparison maps over the same map are homotopic.

## References

* [Stacks Project, Tag 0702](https://stacks.math.columbia.edu/tag/0702)
* [Stacks Project, Tag 0703](https://stacks.math.columbia.edu/tag/0703)
-/

@[expose] public section

namespace Module.PureProjectiveResolution

section

universe u v w


variable {A : Type u} [CommRing A]

/-- An augmentation `P₀ ⟶ M` of a chain complex is a *pure projective resolution* if
`⋯ ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` is universally exact and every `Pᵢ` is pure projective. -/
@[stacks 0702 "pure_projective_resolution"]
public structure IsPureProjectiveResolution
    {M : Type v} [AddCommGroup M] [Module A M]
    (P : ChainComplex (ModuleCat.{w} A) ℕ) (augmentation : P.X 0 →ₗ[A] M) : Prop where
  /-- Exactness at the resolved module. -/
  surjective_augmentation : Function.Surjective augmentation
  /-- Exactness at the resolved module remains true after tensoring. -/
  baseChange_surjective_augmentation : ∀ (Q : Type (max u v w)) [AddCommGroup Q] [Module A Q],
    Function.Surjective (augmentation.rTensor Q)
  /-- The augmented complex is exact at degree zero. -/
  exact_zero : Function.Exact (P.d 1 0) augmentation
  /-- Exactness at degree zero remains true after tensoring. -/
  baseChange_exact_zero : ∀ (Q : Type (max u v w)) [AddCommGroup Q] [Module A Q],
    Function.Exact ((P.d 1 0).hom.rTensor Q) (augmentation.rTensor Q)
  /-- The complex is exact between every three consecutive terms. -/
  exact : ∀ i : ℕ, Function.Exact (P.d (i + 2) (i + 1)) (P.d (i + 1) i)
  /-- Exactness between consecutive terms remains true after tensoring. -/
  baseChange_exact : ∀ (Q : Type (max u v w)) [AddCommGroup Q] [Module A Q] (i : ℕ),
    Function.Exact ((P.d (i + 2) (i + 1)).hom.rTensor Q)
      ((P.d (i + 1) i).hom.rTensor Q)
  /-- Every term of the resolution is pure projective. -/
  pureProjective : ∀ i : ℕ, Module.PureProjective A (P.X i)

end

section

universe u v w


variable {A : Type u} [CommRing A]

/-- A universally exact augmented chain resolution of a module. -/
public structure IsUniversallyExactResolution
    {M : Type v} [AddCommGroup M] [Module A M]
    (C : ChainComplex (ModuleCat.{v} A) ℕ) (augmentation : C.X 0 →ₗ[A] M) : Prop where
  /-- Exactness at the resolved module. -/
  surjective_augmentation : Function.Surjective augmentation
  /-- Exactness at the resolved module remains true after tensoring. -/
  baseChange_surjective_augmentation : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    Function.Surjective (augmentation.rTensor Q)
  /-- The augmented complex is exact at degree zero. -/
  exact_zero : Function.Exact (C.d 1 0) augmentation
  /-- Exactness at degree zero remains true after tensoring. -/
  baseChange_exact_zero : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    Function.Exact ((C.d 1 0).hom.rTensor Q) (augmentation.rTensor Q)
  /-- The complex is exact between every three consecutive terms. -/
  exact : ∀ i : ℕ, Function.Exact (C.d (i + 2) (i + 1)) (C.d (i + 1) i)
  /-- Exactness between consecutive terms remains true after tensoring. -/
  baseChange_exact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q] (i : ℕ),
    Function.Exact ((C.d (i + 2) (i + 1)).hom.rTensor Q)
      ((C.d (i + 1) i).hom.rTensor Q)

private structure ComparisonPrefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (P C : ChainComplex (ModuleCat.{v} A) ℕ)
    (aP : P.X 0 →ₗ[A] M) (aC : C.X 0 →ₗ[A] N) (f : M →ₗ[A] N)
    (n : ℕ) where
  map : (i : ℕ) → P.X i →ₗ[A] C.X i
  initial : aC.comp (map 0) = f.comp aP
  comm : ∀ i, i < n →
    (C.d (i + 1) i).hom.comp (map (i + 1)) =
      (map i).comp (P.d (i + 1) i).hom

private def liftLinearMap {X Y : Type v} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) :
    ULift.{u} X →ₗ[A] ULift.{u} Y :=
  (ULift.moduleEquiv (R := A) (M := Y)).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv (R := A) (M := X)).toLinearMap)

private theorem exact_liftLinearMap_iff {X Y Z : Type v}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) :
    Function.Exact (liftLinearMap (A := A) f) (liftLinearMap (A := A) g) ↔
      Function.Exact f g := by
  apply Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (ULift.moduleEquiv (R := A) (M := X)).symm)
    (e₂ := (ULift.moduleEquiv (R := A) (M := Y)).symm)
    (e₃ := (ULift.moduleEquiv (R := A) (M := Z)).symm)
  · ext x; simp [liftLinearMap]
  · ext x; simp [liftLinearMap]

private theorem exact_liftLinearMap_rTensor_iff {X Y Z : Type v} {Q : Type w}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] [AddCommGroup Q] [Module A Q]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) :
    Function.Exact ((liftLinearMap (A := A) f).rTensor Q)
      ((liftLinearMap (A := A) g).rTensor Q) ↔
      Function.Exact (f.rTensor Q) (g.rTensor Q) := by
  let eX : ULift.{u} X ≃ₗ[A] X := ULift.moduleEquiv
  let eY : ULift.{u} Y ≃ₗ[A] Y := ULift.moduleEquiv
  let eZ : ULift.{u} Z ≃ₗ[A] Z := ULift.moduleEquiv
  apply Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (eX.rTensor Q).symm) (e₂ := (eY.rTensor Q).symm)
    (e₃ := (eZ.rTensor Q).symm)
  · apply TensorProduct.ext'
    intro x q; simp [liftLinearMap, eX, eY, LinearMap.rTensor_comp]
  · apply TensorProduct.ext'
    intro y q; simp [liftLinearMap, eY, eZ, LinearMap.rTensor_comp]

/-- A map out of a pure projective module lifts through a surjection `q` out of a term of a
universally exact resolution whose kernel is the image of the differential. -/
private theorem exists_lift_of_exact_surjective
    {N D X : Type v} [AddCommGroup N] [Module A N] [AddCommGroup D] [Module A D]
    [AddCommGroup X] [Module A X]
    {C : ChainComplex (ModuleCat.{v} A) ℕ} {aC : C.X 0 →ₗ[A] N}
    (hC : IsUniversallyExactResolution C aC) (m : ℕ) (q : C.X m →ₗ[A] D)
    (hqs : Function.Surjective q) (hq : Function.Exact (C.d (m + 1) m) q)
    (hX : Module.PureProjective A X) (r : X →ₗ[A] D) :
    ∃ t : X →ₗ[A] C.X m, q.comp t = r := by
  let d1 := (C.d (m + 1) m).hom
  let d2 := (C.d (m + 2) (m + 1)).hom
  let d1L := liftLinearMap (A := A) d1
  let d2L := liftLinearMap (A := A) d2
  let qL := liftLinearMap (A := A) q
  let S := LinearMap.range d1L
  let uMap : S →ₗ[A] ULift.{u} (C.X m) := S.subtype
  have hu : UniversallyInjective uMap := by
    simpa [uMap, S, d1L, d2L] using
      (Module.universallyInjective_range_subtype d2L d1L
        ((exact_liftLinearMap_iff (A := A) d2 d1).2 (hC.exact m))
        (fun Q _ _ =>
          (exact_liftLinearMap_rTensor_iff (A := A) d2 d1).2
            (hC.baseChange_exact Q m)))
  have hex : Function.Exact uMap qL := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    simpa [d1L, d1, qL] using LinearMap.exact_iff.mp
      ((exact_liftLinearMap_iff (A := A) d1 q).2 hq)
  have hsurj : Function.Surjective qL := by
    intro y
    obtain ⟨x, hx⟩ := hqs y.down
    exact ⟨ULift.up x, by simp [qL, liftLinearMap, hx]⟩
  have hpp := hX S (ULift.{u} (C.X m)) (ULift.{u} D) uMap qL
    (by intro x y h; exact Subtype.ext h) hsurj (LinearMap.exact_iff.mp hex).symm hu
  obtain ⟨tL, htL⟩ := hpp.2.1 ((ULift.moduleEquiv (R := A) (M := D)).symm.toLinearMap.comp r)
  refine ⟨(ULift.moduleEquiv (R := A) (M := C.X m)).toLinearMap.comp tL, ?_⟩
  ext x
  simpa [qL, liftLinearMap] using congrArg ULift.down (LinearMap.congr_fun htL x)

/-- An element of a pure projective module lifts through a differential of a universally exact
resolution if it is killed by a map `q` exact with that differential. -/
private theorem exists_lift_through_differential
    {N M X : Type v} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M]
    [AddCommGroup X] [Module A X]
    {C : ChainComplex (ModuleCat.{v} A) ℕ} {aC : C.X 0 →ₗ[A] N}
    (hC : IsUniversallyExactResolution C aC) (n : ℕ) (q : C.X n →ₗ[A] M)
    (hq : Function.Exact (C.d (n + 1) n) q) (hX : Module.PureProjective A X)
    (r : X →ₗ[A] C.X n) (hr : q.comp r = 0) :
    ∃ t : X →ₗ[A] C.X (n + 1), (C.d (n + 1) n).hom.comp t = r := by
  have hmem : ∀ x, r x ∈ LinearMap.range (C.d (n + 1) n).hom := fun x => by
    rw [← LinearMap.exact_iff.mp hq]
    exact LinearMap.congr_fun hr x
  obtain ⟨t, ht⟩ := exists_lift_of_exact_surjective hC (n + 1)
    (C.d (n + 1) n).hom.rangeRestrict (LinearMap.surjective_rangeRestrict _)
    (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
      exact LinearMap.exact_iff.mp (hC.exact n))
    hX (r.codRestrict _ hmem)
  exact ⟨t, by ext x; simpa using congrArg Subtype.val (LinearMap.congr_fun ht x)⟩

private theorem hom_d_comp_d (C : ChainComplex (ModuleCat.{v} A) ℕ) (i j k : ℕ) :
    (C.d j k).hom.comp (C.d i j).hom = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg (fun f => f.hom) (C.d_comp_d i j k)

private theorem next_comparison_map
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P C : ChainComplex (ModuleCat.{v} A) ℕ}
    {aP : P.X 0 →ₗ[A] M} {aC : C.X 0 →ₗ[A] N} {f : M →ₗ[A] N}
    {n : ℕ} (p : ComparisonPrefix (A := A) P C aP aC f n)
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P aP)
    (hC : IsUniversallyExactResolution C aC) :
    ∃ g : P.X (n + 1) →ₗ[A] C.X (n + 1),
      (C.d (n + 1) n).hom.comp g =
        (p.map n).comp (P.d (n + 1) n).hom := by
  cases n with
  | zero =>
      refine exists_lift_through_differential hC 0 aC hC.exact_zero (hP.pureProjective 1) _ ?_
      rw [← LinearMap.comp_assoc, p.initial, LinearMap.comp_assoc]
      ext x
      simp [Function.Exact.apply_apply_eq_zero hP.exact_zero x]
  | succ k =>
      refine exists_lift_through_differential hC (k + 1) (C.d (k + 1) k).hom (hC.exact k)
        (hP.pureProjective (k + 2)) _ ?_
      rw [← LinearMap.comp_assoc, p.comm k (by omega), LinearMap.comp_assoc,
        hom_d_comp_d, LinearMap.comp_zero]

private noncomputable def extend_comparison_prefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P C : ChainComplex (ModuleCat.{v} A) ℕ}
    {aP : P.X 0 →ₗ[A] M} {aC : C.X 0 →ₗ[A] N} {f : M →ₗ[A] N}
    {n : ℕ} (p : ComparisonPrefix (A := A) P C aP aC f n)
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P aP)
    (hC : IsUniversallyExactResolution C aC) :
    ComparisonPrefix (A := A) P C aP aC f (n + 1) := by
  classical
  let g := Classical.choose (next_comparison_map p hP hC)
  have hg := Classical.choose_spec (next_comparison_map p hP hC)
  let newMap : (i : ℕ) → P.X i →ₗ[A] C.X i :=
    fun i => if h : i = n + 1 then h.symm ▸ g else p.map i
  refine ⟨newMap, ?_, ?_⟩
  · simpa [newMap, show (0 : ℕ) ≠ n + 1 by omega] using p.initial
  · intro i hi
    by_cases hlt : i < n
    · have hne : i + 1 ≠ n + 1 := by omega
      have hne' : i ≠ n := by omega
      have hne'' : i ≠ n + 1 := by omega
      simpa [newMap, hne, hne', hne''] using p.comm i hlt
    · have hie : i = n := by omega
      subst i
      have hne : n ≠ n + 1 := by omega
      simpa [newMap, hne] using hg

private noncomputable def initial_comparison_prefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P C : ChainComplex (ModuleCat.{v} A) ℕ}
    (aP : P.X 0 →ₗ[A] M) (aC : C.X 0 →ₗ[A] N) (f : M →ₗ[A] N)
    (g0 : P.X 0 →ₗ[A] C.X 0) (hg0 : aC.comp g0 = f.comp aP) :
    ComparisonPrefix (A := A) P C aP aC f 0 := by
  let initialMap : (i : ℕ) → P.X i →ₗ[A] C.X i :=
    fun i => if h : i = 0 then h.symm ▸ g0 else 0
  refine ⟨initialMap, ?_, ?_⟩
  · simpa [initialMap] using hg0
  · intro i hi; omega

/-- A module map extends from a pure projective resolution to any universally
exact resolution. -/
@[stacks 0703 "comparison_map"]
public theorem exists_comparison_map
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (P C : ChainComplex (ModuleCat.{v} A) ℕ)
    (aP : P.X 0 →ₗ[A] M) (aC : C.X 0 →ₗ[A] N)
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P aP)
    (hC : IsUniversallyExactResolution C aC) :
    ∃ F : P ⟶ C, aC.comp (F.f 0).hom = f.comp aP := by
  classical
  obtain ⟨g0, hg0⟩ := exists_lift_of_exact_surjective hC 0 aC hC.surjective_augmentation
    hC.exact_zero (hP.pureProjective 0) (f.comp aP)
  let prefixes : ∀ n, ComparisonPrefix (A := A) P C aP aC f n :=
    Nat.rec (initial_comparison_prefix aP aC f g0 hg0)
      (fun n p => extend_comparison_prefix p hP hC)
  let F : P ⟶ C := HomologicalComplex.Hom.mk
    (fun i => ModuleCat.ofHom (prefixes i |>.map i))
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      rcases hij with rfl
      apply ModuleCat.hom_ext
      have hmap : ((prefixes (j + 1)).map j) = ((prefixes j).map j) := by
        simp [prefixes, extend_comparison_prefix]
      have hcomm := (prefixes (j + 1)).comm j (Nat.lt_succ_self j)
      rw [hmap] at hcomm
      exact hcomm)
  exact ⟨F, (prefixes 0).initial⟩

end

section

universe u v


open CategoryTheory

variable {A : Type u} [CommRing A]

private theorem residual_comp_differential_zero
    {P C : ChainComplex (ModuleCat.{v} A) ℕ}
    (γ : P ⟶ C) (n : ℕ)
    (s : P.X n ⟶ C.X (n + 1))
    (t : P.X (n + 1) ⟶ C.X (n + 2))
    (hs : γ.f (n + 1) = P.d (n + 1) n ≫ s + t ≫ C.d (n + 2) (n + 1)) :
    (C.d (n + 2) (n + 1)).hom.comp
        ((γ.f (n + 2)).hom - t.hom.comp (P.d (n + 2) (n + 1)).hom) = 0 := by
  have hchain : (C.d (n + 2) (n + 1)).hom.comp (γ.f (n + 2)).hom =
      (γ.f (n + 1)).hom.comp (P.d (n + 2) (n + 1)).hom := by
    simpa only [ModuleCat.hom_comp] using congrArg (fun f => f.hom) (γ.comm (n + 2) (n + 1))
  have hs' : (γ.f (n + 1)).hom = s.hom.comp (P.d (n + 1) n).hom +
      (C.d (n + 2) (n + 1)).hom.comp t.hom := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_add] using congrArg (fun f => f.hom) hs
  calc
    _ = (C.d (n + 2) (n + 1)).hom.comp (γ.f (n + 2)).hom -
        ((C.d (n + 2) (n + 1)).hom.comp t.hom).comp (P.d (n + 2) (n + 1)).hom := by
      simp [LinearMap.comp_sub, LinearMap.comp_assoc]
    _ = (γ.f (n + 1)).hom.comp (P.d (n + 2) (n + 1)).hom -
        ((C.d (n + 2) (n + 1)).hom.comp t.hom).comp (P.d (n + 2) (n + 1)).hom := by
      rw [hchain]
    _ = 0 := by
      rw [hs']
      simp only [LinearMap.add_comp, LinearMap.comp_assoc]
      rw [hom_d_comp_d]
      simp

/-- Two maps of resolutions inducing the same map of resolved modules are homotopic. -/
@[stacks 0703 "homotopy_uniqueness"]
public theorem homotopy_of_same_augmentation
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (P C : ChainComplex (ModuleCat.{v} A) ℕ)
    (augmentationP : P.X 0 →ₗ[A] M) (augmentationC : C.X 0 →ₗ[A] N)
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P augmentationP)
    (hC : Module.PureProjectiveResolution.IsUniversallyExactResolution C augmentationC)
    (f : M →ₗ[A] N) (α β : P ⟶ C)
    (hα : augmentationC.comp (α.f 0).hom = f.comp augmentationP)
    (hβ : augmentationC.comp (β.f 0).hom = f.comp augmentationP) :
    Nonempty (Homotopy α β) := by
  let γ : P ⟶ C := α - β
  have hγ0 : augmentationC.comp (γ.f 0).hom = 0 := by
    simp [γ, LinearMap.comp_sub, hα, hβ]
  obtain ⟨h0, hh0⟩ := exists_lift_through_differential hC 0
    augmentationC hC.exact_zero (hP.pureProjective 0) (γ.f 0).hom hγ0
  let z : P.X 0 ⟶ C.X 1 := ModuleCat.ofHom h0
  have hz : γ.f 0 = z ≫ C.d 1 0 := by
    apply ModuleCat.hom_ext
    exact hh0.symm
  let r1 : P.X 1 →ₗ[A] C.X 1 :=
    (γ.f 1).hom - h0.comp (P.d 1 0).hom
  have hr1 : (C.d 1 0).hom.comp r1 = 0 := by
    have hchain : (C.d 1 0).hom.comp (γ.f 1).hom = (γ.f 0).hom.comp (P.d 1 0).hom := by
      simpa only [ModuleCat.hom_comp] using congrArg (fun k => k.hom) (γ.comm 1 0)
    rw [LinearMap.comp_sub, hchain, ← LinearMap.comp_assoc, hh0]
    simp
  obtain ⟨h1, hh1⟩ := exists_lift_through_differential hC 1
    (C.d 1 0).hom (hC.exact 0) (hP.pureProjective 1) r1 hr1
  let z1 : P.X 1 ⟶ C.X 2 := ModuleCat.ofHom h1
  have hone : γ.f 1 = P.d 1 0 ≫ z + z1 ≫ C.d 2 1 := by
    apply ModuleCat.hom_ext
    change (γ.f 1).hom = h0.comp (P.d 1 0).hom + (C.d 2 1).hom.comp h1
    rw [hh1]
    dsimp [r1]
    abel
  refine ⟨(Homotopy.equivSubZero (f := α) (g := β)).symm
    (Homotopy.mkInductive γ z hz z1 hone ?_)⟩
  intro n p
  let r : P.X (n + 2) →ₗ[A] C.X (n + 2) :=
    (γ.f (n + 2)).hom - p.2.1.hom.comp (P.d (n + 2) (n + 1)).hom
  have hr' : (C.d (n + 2) (n + 1)).hom.comp r = 0 := by
    simpa [r] using residual_comp_differential_zero γ n p.1 p.2.1 p.2.2
  let witness := exists_lift_through_differential hC (n + 2)
    (C.d (n + 2) (n + 1)).hom (hC.exact (n + 1)) (hP.pureProjective (n + 2)) r hr'
  let hn := Classical.choose witness
  have hhn := Classical.choose_spec witness
  refine ⟨ModuleCat.ofHom hn, ?_⟩
  apply ModuleCat.hom_ext
  change (γ.f (n + 2)).hom = p.2.1.hom.comp (P.d (n + 2) (n + 1)).hom +
    (C.d (n + 3) (n + 2)).hom.comp hn
  rw [hhn]
  dsimp [r]
  abel

end

end Module.PureProjectiveResolution

end
