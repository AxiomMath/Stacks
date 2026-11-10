module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic

/-!
# The determinant submodule of a product

Let `R` be a commutative ring. For a module `M` the determinant submodule of its exterior algebra is
the joint kernel of left multiplication by the degree-one generators. This file develops its basic
properties for finite projective modules and constructs the equivalence
`det A ⊗ det B ≃ det (A × B)` used to build the determinant isomorphism of a short exact sequence.

## Main results

* `ProjectiveDeterminant.range_mapIncl_ker_eq_ker_rTensor_inf_ker_lTensor`: for flat modules, the
  image of `ker f ⊗ ker g` is the intersection of the kernels of `f ⊗ B` and `A ⊗ g`.
-/

namespace ProjectiveDeterminant

/-! ### The determinant of a short exact sequence -/

section

universe u v w x

open DirectSum
open scoped TensorProduct

private theorem exteriorPower_projective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨k, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  apply Module.Projective.of_split (exteriorPower.map n g) (exteriorPower.map n f)
  rw [← exteriorPower.map_comp, hfg, exteriorPower.map_id]

private theorem exteriorAlgebra_projective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Projective R (ExteriorAlgebra R M) := by
  let (n : ℕ) : Module.Projective R (⋀[R]^n M) := exteriorPower_projective n
  let : Module.Projective R (⨁ n, ⋀[R]^n M) := inferInstance
  let e : ExteriorAlgebra R M ≃ₗ[R] ⨁ n, ⋀[R]^n M :=
    DirectSum.decomposeLinearEquiv (fun n => ⋀[R]^n M)
  exact Module.Projective.of_equiv' e.symm

private noncomputable def exactEquivProdData
    {R : Type u} [CommRing R]
    {M' : Type v} {M : Type w} {M'' : Type x}
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M''] [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    {e : M ≃ₗ[R] M' × M'' //
      (∀ a : M', e (f a) = (a, 0)) ∧ (∀ m : M, (e m).2 = g m)} := by
  classical
  let s := Classical.choose (g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg))
  have hs : g ∘ₗ s = LinearMap.id := Classical.choose_spec
    (g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg))
  have hsx (b : M'') : g (s b) = b := LinearMap.congr_fun hs b
  let k := LinearMap.ker g
  let f' : M' →ₗ[R] k := f.codRestrict k fun z => LinearMap.mem_ker.2 ((hfg (f z)).2 ⟨z, rfl⟩)
  have hf' : Function.Bijective f' := by
    refine ⟨fun a b hab => hf (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨a, ha⟩ := (hfg (y : M)).1 y.2
    exact ⟨a, Subtype.ext ha⟩
  let e₁ : M' ≃ₗ[R] k := LinearEquiv.ofBijective f' hf'
  let q : k × M'' →ₗ[R] M :=
    (k.subtype.comp (LinearMap.fst R k M'')) + s.comp (LinearMap.snd R k M'')
  have hq : Function.Bijective q := by
    constructor
    · intro a b hab
      have hqa : g (q a) = a.2 := by simp [q, hsx]
      have hqb : g (q b) = b.2 := by simp [q, hsx]
      have hb : a.2 = b.2 := by
        rw [← hqa, ← hqb]
        exact congrArg g hab
      have hka : q a - s (g (q a)) = (a.1 : M) := by simp [q, hsx]
      have hkb : q b - s (g (q b)) = (b.1 : M) := by simp [q, hsx]
      have ha : (a.1 : M) = (b.1 : M) := by
        calc
          (a.1 : M) = q a - s (g (q a)) := hka.symm
          _ = q b - s (g (q b)) := congrArg (fun z : M => z - s (g z)) hab
          _ = (b.1 : M) := hkb
      exact Prod.ext (Subtype.ext ha) hb
    · intro m
      refine ⟨(⟨m - s (g m), LinearMap.mem_ker.2 ?_⟩, g m), ?_⟩
      · rw [map_sub, hsx]
        simp
      · simp [q, LinearMap.add_apply]
  let e₂ : (k × M'') ≃ₗ[R] M := LinearEquiv.ofBijective q hq
  let e := e₂.symm.trans (e₁.prodCongr (LinearEquiv.refl R M'')).symm
  refine ⟨e, ?_, ?_⟩
  · intro a
    have he : e₂ (e₁ a, 0) = f a := by
      simp [e₂, q, e₁, f']
    have he' : e₂.symm (f a) = (e₁ a, 0) := by
      apply e₂.injective
      simpa using he.symm
    simp [e, he']
  · intro m
    have he (t : k × M'') : g (e₂ t) = t.2 := by simp [e₂, q, hsx]
    have hm : (e₂.symm m).2 = g m := by
      rw [← he (e₂.symm m), e₂.apply_symm_apply]
    simpa [e] using hm

private noncomputable def exactEquivProd
    {R : Type u} [CommRing R]
    {M' : Type v} {M : Type w} {M'' : Type x}
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M''] [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    M ≃ₗ[R] M' × M'' :=
  (exactEquivProdData f g hf hfg hg).1

private abbrev determinantSubmodule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))

private noncomputable def exteriorGradeInvolution {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M := by
  let f : M →ₗ[R] M := -LinearMap.id
  let h : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M := ExteriorAlgebra.map f
  have hh : h.comp h = AlgHom.id R _ := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp [h, f]
  exact AlgEquiv.ofAlgHom h h hh hh

private theorem exteriorGradeInvolution_involutive {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (x : ExteriorAlgebra R M) :
    exteriorGradeInvolution (R := R) (M := M)
      (exteriorGradeInvolution (R := R) (M := M) x) = x := by
  let f : M →ₗ[R] M := -LinearMap.id
  change (ExteriorAlgebra.map f) ((ExteriorAlgebra.map f) x) = x
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  simp [f]

/-- In an exterior algebra, left and right multiplication by a degree-one generator have the
same kernel. -/
private theorem mulLeft_ι_eq_zero_iff_mulRight {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x = 0 ↔ x * ExteriorAlgebra.ι R m = 0 := by
  have hanti (z : ExteriorAlgebra R M) :
      ExteriorAlgebra.ι R m * z =
        exteriorGradeInvolution (R := R) (M := M) z * ExteriorAlgebra.ι R m := by
    refine ExteriorAlgebra.induction
      (C := fun z => ExteriorAlgebra.ι R m * z =
        exteriorGradeInvolution (R := R) (M := M) z * ExteriorAlgebra.ι R m)
      ?_ ?_ ?_ ?_ z
    · intro r
      simp [exteriorGradeInvolution, Algebra.commutes]
    · intro n
      simp only [exteriorGradeInvolution, AlgEquiv.ofAlgHom_apply,
        ExteriorAlgebra.map_apply_ι]
      change ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R n =
        ExteriorAlgebra.ι R (-n) * ExteriorAlgebra.ι R m
      simpa only [map_neg, neg_mul] using
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m n)
    · intro a b ha hb
      calc
        ExteriorAlgebra.ι R m * (a * b) =
            (ExteriorAlgebra.ι R m * a) * b := by rw [mul_assoc]
        _ = (exteriorGradeInvolution (R := R) (M := M) a *
            ExteriorAlgebra.ι R m) * b := by rw [ha]
        _ = exteriorGradeInvolution (R := R) (M := M) a *
            (ExteriorAlgebra.ι R m * b) := by rw [mul_assoc]
        _ = exteriorGradeInvolution (R := R) (M := M) a *
            (exteriorGradeInvolution (R := R) (M := M) b *
              ExteriorAlgebra.ι R m) := by rw [hb]
        _ = (exteriorGradeInvolution (R := R) (M := M) a *
            exteriorGradeInvolution (R := R) (M := M) b) *
              ExteriorAlgebra.ι R m := by rw [mul_assoc]
        _ = exteriorGradeInvolution (R := R) (M := M) (a * b) *
            ExteriorAlgebra.ι R m :=
              congrArg (fun z => z * ExteriorAlgebra.ι R m)
                ((exteriorGradeInvolution (R := R) (M := M)).map_mul a b).symm
    · intro a b ha hb
      rw [mul_add, ha, hb, ← add_mul]
      exact congrArg (fun z => z * ExteriorAlgebra.ι R m)
        ((exteriorGradeInvolution (R := R) (M := M)).map_add a b).symm
  have hg (y : ExteriorAlgebra R M) (h : y * ExteriorAlgebra.ι R m = 0) :
      exteriorGradeInvolution (R := R) (M := M) y * ExteriorAlgebra.ι R m = 0 := by
    have hh := congrArg (exteriorGradeInvolution (R := R) (M := M)) h
    rw [map_mul, map_zero] at hh
    have hi : exteriorGradeInvolution (R := R) (M := M) (ExteriorAlgebra.ι R m) =
        -ExteriorAlgebra.ι R m := by simp [exteriorGradeInvolution]
    rw [hi] at hh
    exact neg_eq_zero.mp (by simpa [neg_mul] using hh)
  constructor
  · intro h
    have h' := hg _ (by rw [← hanti x]; exact h)
    simpa [exteriorGradeInvolution_involutive] using h'
  · intro h
    rw [hanti]
    exact hg _ h

private def annMap {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : ι → M) : ExteriorAlgebra R M →ₗ[R] (ι → ExteriorAlgebra R M) :=
  LinearMap.pi fun i => LinearMap.mulLeft R (ExteriorAlgebra.ι R (s i))

private def annMapRight {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : ι → M) : ExteriorAlgebra R M →ₗ[R] (ι → ExteriorAlgebra R M) :=
  LinearMap.pi fun i => LinearMap.mulRight R (ExteriorAlgebra.ι R (s i))

/-- A linear map vanishing on a spanning family vanishes. -/
private theorem map_eq_zero_of_span_eq_top {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {s : ι → M} (hs : Submodule.span R (Set.range s) = ⊤)
    (h : M →ₗ[R] N) (hi : ∀ i, h (s i) = 0) (a : M) : h a = 0 :=
  LinearMap.congr_fun (LinearMap.ext_on_range (g := 0) hs hi) a

/-- A finite spanning family suffices to test membership in the determinant submodule. -/
private theorem determinantSubmodule_eq_ker_annMap {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {ι : Type*}
    (s : ι → M) (hs : Submodule.span R (Set.range s) = ⊤) :
    determinantSubmodule (R := R) (M := M) = LinearMap.ker (annMap s) := by
  classical
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  rw [annMap]
  simp only [LinearMap.pi_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro hx i
    exact hx (s i)
  · intro hx m
    exact map_eq_zero_of_span_eq_top hs
      ((LinearMap.mulRight R x).comp (ExteriorAlgebra.ι R)) hx m

private theorem determinantSubmodule_eq_ker_annMapRight {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {ι : Type*}
    (s : ι → M) (hs : Submodule.span R (Set.range s) = ⊤) :
    determinantSubmodule (R := R) (M := M) = LinearMap.ker (annMapRight s) := by
  rw [determinantSubmodule_eq_ker_annMap s hs]
  ext x
  simp only [LinearMap.mem_ker, annMap, annMapRight, LinearMap.pi_apply,
    Pi.zero_apply, funext_iff]
  exact forall_congr' fun i => mulLeft_ι_eq_zero_iff_mulRight (s i) x

/-- The determinant submodule of a finite projective module is projective. -/
private theorem determinantSubmodule_projective {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Projective R (determinantSubmodule (R := R) (M := M)) := by
  let e : ProjectiveDeterminant.module (R := R) (M := M) ≃ₗ[R]
      determinantSubmodule (R := R) (M := M) :=
    LinearEquiv.ofEq _ _ (determinant_submodule_eq_annihilator R M)
  let : Module.Invertible R (ProjectiveDeterminant.module (R := R) (M := M)) :=
    ProjectiveDeterminant.invertible
  exact Module.Projective.of_equiv e

/-- The exterior algebra map of an equivalence sends the determinant submodule into the target's. -/
private theorem map_mem_determinantSubmodule {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : ExteriorAlgebra R M} (hx : x ∈ determinantSubmodule (R := R) (M := M)) :
    ExteriorAlgebra.map e.toLinearMap x ∈ determinantSubmodule (R := R) (M := N) := by
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro n
  simpa using congrArg (ExteriorAlgebra.map e.toLinearMap) (hx (e.symm n))

/-- A linear equivalence of modules induces an equivalence of their determinant submodules. -/
private noncomputable def determinantSubmodule_mapEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    determinantSubmodule (R := R) (M := M) ≃ₗ[R]
      determinantSubmodule (R := R) (M := N) := by
  let F : determinantSubmodule (R := R) (M := M) →ₗ[R]
      determinantSubmodule (R := R) (M := N) :=
    ((ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp
      (determinantSubmodule (R := R) (M := M)).subtype).codRestrict _
        fun x => map_mem_determinantSubmodule e x.2
  let G : determinantSubmodule (R := R) (M := N) →ₗ[R]
      determinantSubmodule (R := R) (M := M) :=
    ((ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap.comp
      (determinantSubmodule (R := R) (M := N)).subtype).codRestrict _
        fun x => map_mem_determinantSubmodule e.symm x.2
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  · ext x
    change ExteriorAlgebra.map e.toLinearMap
        (ExteriorAlgebra.map e.symm.toLinearMap x.1) = x.1
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp
  · ext x
    change ExteriorAlgebra.map e.symm.toLinearMap
        (ExteriorAlgebra.map e.toLinearMap x.1) = x.1
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp

/-- Tensoring a kernel with a flat module preserves the kernel. -/
private noncomputable def kerLTensorEquivOfFlat
    {R A B P : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup P] [Module R P] [Module.Flat R P]
    (f : A →ₗ[R] B) :
    TensorProduct R P (LinearMap.ker f) ≃ₗ[R] LinearMap.ker (f.lTensor P) :=
  LinearMap.tensorKerEquiv R P f

private noncomputable def kerCongr
    {R A B C D : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (e : A ≃ₗ[R] B) (d : C ≃ₗ[R] D)
    (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    (h : d.toLinearMap.comp f = g.comp e.toLinearMap) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g := by
  let F : LinearMap.ker f →ₗ[R] LinearMap.ker g :=
    ((e.toLinearMap.comp (LinearMap.ker f).subtype).codRestrict _ (by
      intro x
      have hx := congrArg (fun k : A →ₗ[R] D => k x) h
      simpa [LinearMap.comp_apply, x.2] using hx.symm))
  let G : LinearMap.ker g →ₗ[R] LinearMap.ker f :=
    ((e.symm.toLinearMap.comp (LinearMap.ker g).subtype).codRestrict _ (by
      intro y
      have hy := congrArg (fun k : A →ₗ[R] D => k (e.symm y)) h
      have hy' : d (f (e.symm y)) = 0 := by
        simpa [LinearMap.comp_apply, y.2] using hy
      exact (show f (e.symm y) = 0 from d.injective (by simpa using hy'))))
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e (e.symm x.1) = x.1
    simp
  · apply LinearMap.ext
    intro y
    apply Subtype.ext
    change e.symm (e y.1) = y.1
    simp

private noncomputable def kerRTensorEquivOfFlat
    {R A B P : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup P] [Module R P] [Module.Flat R P]
    (f : A →ₗ[R] B) :
    LinearMap.ker (f.rTensor P) ≃ₗ[R]
      TensorProduct R (LinearMap.ker f) P := by
  let e₁ := kerCongr (TensorProduct.comm R A P) (TensorProduct.comm R B P)
    (f.rTensor P) (f.lTensor P) (by
      ext a p
      simp [TensorProduct.comm_tmul])
  exact e₁.trans (kerLTensorEquivOfFlat (R := R) (P := P) f).symm |>.trans
    (TensorProduct.comm R P (LinearMap.ker f))

private theorem tensorKerInf
    {R A B C D : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    [Module.Flat R B] [Module.Flat R D]
    (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    [Module.Flat R (LinearMap.ker f)] :
    LinearMap.range (TensorProduct.mapIncl (LinearMap.ker f) (LinearMap.ker g)) =
      LinearMap.ker (f.rTensor B) ⊓ LinearMap.ker (g.lTensor A) := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    constructor
    · change f.rTensor B (TensorProduct.mapIncl f.ker g.ker x) = 0
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.mapIncl]
      | add x y hx hy => simp [hx, hy]
    · change g.lTensor A (TensorProduct.mapIncl f.ker g.ker x) = 0
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.mapIncl]
      | add x y hx hy => simp [hx, hy]
  · intro z hz
    have hzF : z ∈ LinearMap.ker (f.rTensor B) := hz.1
    have hzG : z ∈ LinearMap.ker (g.lTensor A) := hz.2
    let e₁ : LinearMap.ker (f.rTensor B) ≃ₗ[R] f.ker ⊗[R] B :=
      kerRTensorEquivOfFlat (P := B) f
    let x : f.ker ⊗[R] B := e₁ ⟨z, hzF⟩
    have hx : f.ker.subtype.rTensor B x = z := by
      have hco (t : f.ker ⊗[R] B) :
          ((e₁.symm t : LinearMap.ker (f.rTensor B)) : A ⊗[R] B) =
            f.ker.subtype.rTensor B t := by
        induction t using TensorProduct.inductionOn with
        | tmul a b => rfl
        | add a b ha hb => simp [ha, hb]
      rw [← hco x]
      exact congrArg Subtype.val (e₁.symm_apply_apply ⟨z, hzF⟩)
    have hcomp : (f.ker.subtype.rTensor D) (g.lTensor f.ker x) =
        g.lTensor A (f.ker.subtype.rTensor B x) := by
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp
      | add x y hx hy => simp [hx, hy]
    have hD : Function.Injective (f.ker.subtype.rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ f.ker.subtype_injective
    have hxg : g.lTensor f.ker x = 0 := hD (by rw [hcomp, hx]; exact hzG)
    let y : f.ker ⊗[R] g.ker := (LinearMap.tensorKerEquiv R f.ker g).symm ⟨x, hxg⟩
    refine ⟨y, ?_⟩
    calc
      TensorProduct.mapIncl f.ker g.ker y =
          f.ker.subtype.rTensor B (g.ker.subtype.lTensor f.ker y) := by
            induction y using TensorProduct.inductionOn with
            | tmul a b => rfl
            | add x y hx hy => simp [hx, hy]
      _ = f.ker.subtype.rTensor B x := by
        congr 1
        exact LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm R f.ker g ⟨x, hxg⟩
      _ = z := hx

/-- For flat `B`, `D` and a flat kernel `ker f`, the image of `ker f ⊗ ker g` in `A ⊗ B` is the
intersection of the kernels of `f ⊗ B` and `A ⊗ g`. -/
public alias range_mapIncl_ker_eq_ker_rTensor_inf_ker_lTensor := tensorKerInf

/-- The underlying module equivalence of the exterior-algebra product equivalence. -/
private noncomputable def exteriorProdTensorEquiv {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] :
    ExteriorAlgebra R (A × B) ≃ₗ[R]
      ExteriorAlgebra R A ⊗[R] ExteriorAlgebra R B :=
  (ExteriorAlgebra.prodEquivTensor R A B).toLinearEquiv.trans
    (GradedTensorProduct.of R (fun i : ℕ => ⋀[R]^i A) (fun i : ℕ => ⋀[R]^i B)).symm

private theorem exteriorProdTensorEquiv_symm_tmul {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (a : ExteriorAlgebra R A) (b : ExteriorAlgebra R B) :
    (exteriorProdTensorEquiv (R := R) (A := A) (B := B)).symm (a ⊗ₜ[R] b) =
      ExteriorAlgebra.map (LinearMap.inl R A B) a *
        ExteriorAlgebra.map (LinearMap.inr R A B) b :=
  ExteriorAlgebra.prodEquivTensor_symm_tmul R A B a b

private theorem exteriorProdTensorEquiv_ι_left_mul {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (a : A) (z : ExteriorAlgebra R (A × B)) :
    exteriorProdTensorEquiv (R := R) (A := A) (B := B)
        (ExteriorAlgebra.ι R (a, 0) * z) =
      (LinearMap.mulLeft R (ExteriorAlgebra.ι R a)).rTensor (ExteriorAlgebra R B)
        (exteriorProdTensorEquiv z) := by
  let e := exteriorProdTensorEquiv (R := R) (A := A) (B := B)
  have h (t : ExteriorAlgebra R A ⊗[R] ExteriorAlgebra R B) :
      e (ExteriorAlgebra.ι R (a, 0) * e.symm t) =
        (LinearMap.mulLeft R (ExteriorAlgebra.ι R a)).rTensor
          (ExteriorAlgebra R B) t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [exteriorProdTensorEquiv_symm_tmul]
      have ha : ExteriorAlgebra.ι R (a, 0) =
          ExteriorAlgebra.map (LinearMap.inl R A B) (ExteriorAlgebra.ι R a) := by simp
      rw [ha, ← mul_assoc, ← map_mul, ← exteriorProdTensorEquiv_symm_tmul]
      simp [e, LinearMap.mulLeft]
    | add x y hx hy => simp [mul_add, hx, hy]
  simpa [e] using h (e z)

private theorem exteriorProdTensorEquiv_mul_ι_right {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (b : B) (z : ExteriorAlgebra R (A × B)) :
    exteriorProdTensorEquiv (R := R) (A := A) (B := B)
        (z * ExteriorAlgebra.ι R (0, b)) =
      (LinearMap.mulRight R (ExteriorAlgebra.ι R b)).lTensor (ExteriorAlgebra R A)
        (exteriorProdTensorEquiv z) := by
  let e := exteriorProdTensorEquiv (R := R) (A := A) (B := B)
  have h (t : ExteriorAlgebra R A ⊗[R] ExteriorAlgebra R B) :
      e (e.symm t * ExteriorAlgebra.ι R (0, b)) =
        (LinearMap.mulRight R (ExteriorAlgebra.ι R b)).lTensor
          (ExteriorAlgebra R A) t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [exteriorProdTensorEquiv_symm_tmul]
      have hb : ExteriorAlgebra.ι R (0, b) =
          ExteriorAlgebra.map (LinearMap.inr R A B) (ExteriorAlgebra.ι R b) := by simp
      rw [hb, mul_assoc, ← map_mul, ← exteriorProdTensorEquiv_symm_tmul]
      simp [e, LinearMap.mulRight]
    | add x y hx hy => simp [add_mul, hx, hy]
  simpa [e] using h (e z)

private theorem pi_rTensor_eq_zero_iff {R A B C ι : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Finite ι]
    (fs : ι → A →ₗ[R] C) (z : A ⊗[R] B) :
    (LinearMap.pi fs).rTensor B z = 0 ↔ ∀ i, (fs i).rTensor B z = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := TensorProduct.piLeft R B (fun _ : ι => C)
  have hproj (i : ι) (t : (ι → C) ⊗[R] B) :
      (e t) i = (LinearMap.proj i).rTensor B t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [e, TensorProduct.piLeft, TensorProduct.piRight]
    | add x y hx hy => simp [hx, hy]
  have hcomp (i : ι) :
      (LinearMap.proj i).rTensor B ∘ₗ (LinearMap.pi fs).rTensor B =
        (fs i).rTensor B := by
    ext x y
    simp
  constructor
  · intro hz i
    have hi := congrArg (fun t : (ι → C) ⊗[R] B => (e t) i) hz
    simpa [hproj, ← LinearMap.comp_apply, hcomp] using hi
  · intro hz
    apply e.injective
    ext i
    rw [map_zero, hproj, ← LinearMap.comp_apply, hcomp]
    exact hz i

private theorem pi_lTensor_eq_zero_iff {R A B C ι : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Finite ι]
    (fs : ι → B →ₗ[R] C) (z : A ⊗[R] B) :
    (LinearMap.pi fs).lTensor A z = 0 ↔ ∀ i, (fs i).lTensor A z = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := TensorProduct.piRight R R A (fun _ : ι => C)
  have hproj (i : ι) (t : A ⊗[R] (ι → C)) :
      (e t) i = (LinearMap.proj i).lTensor A t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [e, TensorProduct.piRight]
    | add x y hx hy => simp [hx, hy]
  have hcomp (i : ι) :
      (LinearMap.proj i).lTensor A ∘ₗ (LinearMap.pi fs).lTensor A =
        (fs i).lTensor A := by
    ext x y
    simp
  constructor
  · intro hz i
    have hi := congrArg (fun t : A ⊗[R] (ι → C) => (e t) i) hz
    simpa [hproj, ← LinearMap.comp_apply, hcomp] using hi
  · intro hz
    apply e.injective
    ext i
    rw [map_zero, hproj, ← LinearMap.comp_apply, hcomp]
    exact hz i

private theorem exteriorProdTensorEquiv_mem_joint_ker_iff
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {n m : ℕ} (s : Fin n → A) (t : Fin m → B)
    (hs : Submodule.span R (Set.range s) = ⊤)
    (ht : Submodule.span R (Set.range t) = ⊤)
    (z : ExteriorAlgebra R (A × B)) :
    exteriorProdTensorEquiv z ∈
        LinearMap.ker ((annMap s).rTensor (ExteriorAlgebra R B)) ⊓
          LinearMap.ker ((annMapRight t).lTensor (ExteriorAlgebra R A)) ↔
      z ∈ determinantSubmodule (R := R) (M := A × B) := by
  let e := exteriorProdTensorEquiv (R := R) (A := A) (B := B)
  have hfirst :
      (annMap s).rTensor (ExteriorAlgebra R B) (e z) = 0 ↔
        ∀ i, ExteriorAlgebra.ι R (s i, 0) * z = 0 := by
    change (LinearMap.pi (fun i => LinearMap.mulLeft R (ExteriorAlgebra.ι R (s i)))).rTensor
        (ExteriorAlgebra R B) (e z) = 0 ↔ _
    rw [pi_rTensor_eq_zero_iff]
    exact forall_congr' fun i => by
      rw [← exteriorProdTensorEquiv_ι_left_mul]
      exact (e.map_zero).symm ▸ e.injective.eq_iff
  have hsecond :
      (annMapRight t).lTensor (ExteriorAlgebra R A) (e z) = 0 ↔
        ∀ i, z * ExteriorAlgebra.ι R (0, t i) = 0 := by
    change (LinearMap.pi (fun i => LinearMap.mulRight R (ExteriorAlgebra.ι R (t i)))).lTensor
        (ExteriorAlgebra R A) (e z) = 0 ↔ _
    rw [pi_lTensor_eq_zero_iff]
    exact forall_congr' fun i => by
      rw [← exteriorProdTensorEquiv_mul_ι_right]
      exact (e.map_zero).symm ▸ e.injective.eq_iff
  have hspanA :
      (∀ i, ExteriorAlgebra.ι R (s i, 0) * z = 0) ↔
        ∀ a : A, ExteriorAlgebra.ι R (a, 0) * z = 0 := by
    constructor
    · intro hi a
      exact map_eq_zero_of_span_eq_top hs ((LinearMap.mulRight R z).comp
        ((ExteriorAlgebra.ι R).comp (LinearMap.inl R A B))) hi a
    · intro ha i
      exact ha (s i)
  have hspanB :
      (∀ i, z * ExteriorAlgebra.ι R (0, t i) = 0) ↔
        ∀ b : B, z * ExteriorAlgebra.ι R (0, b) = 0 := by
    constructor
    · intro hi b
      exact map_eq_zero_of_span_eq_top ht ((LinearMap.mulLeft R z).comp
        ((ExteriorAlgebra.ι R).comp (LinearMap.inr R A B))) hi b
    · intro hb i
      exact hb (t i)
  change ((annMap s).rTensor (ExteriorAlgebra R B) (e z) = 0 ∧
      (annMapRight t).lTensor (ExteriorAlgebra R A) (e z) = 0) ↔
        z ∈ determinantSubmodule (R := R) (M := A × B)
  rw [hfirst, hsecond, hspanA, hspanB]
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨ha, hb⟩ p
    have hb' : ExteriorAlgebra.ι R (0, p.2) * z = 0 :=
      (mulLeft_ι_eq_zero_iff_mulRight (0, p.2) z).2 (hb p.2)
    have hp : ExteriorAlgebra.ι R p =
        ExteriorAlgebra.ι R (p.1, 0) + ExteriorAlgebra.ι R (0, p.2) := by
      simpa using (map_add (ExteriorAlgebra.ι R) (p.1, 0) (0, p.2))
    change ExteriorAlgebra.ι R p * z = 0
    rw [hp, add_mul, ha p.1, hb', add_zero]
  · intro hp
    have hp' (p : A × B) : ExteriorAlgebra.ι R p * z = 0 := hp p
    constructor
    · intro a
      exact hp' (a, 0)
    · intro b
      exact (mulLeft_ι_eq_zero_iff_mulRight (0, b) z).1 (hp' (0, b))

private def determinantSubmodule_prodEquiv_property
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : TensorProduct R (determinantSubmodule (R := R) (M := A))
      (determinantSubmodule (R := R) (M := B)) ≃ₗ[R]
        determinantSubmodule (R := R) (M := A × B)) : Prop :=
  ∀ (a : determinantSubmodule (R := R) (M := A))
    (b : determinantSubmodule (R := R) (M := B)),
    (e (a ⊗ₜ[R] b)).1 =
      ExteriorAlgebra.map (LinearMap.inl R A B) (a : ExteriorAlgebra R A) *
        ExteriorAlgebra.map (LinearMap.inr R A B) (b : ExteriorAlgebra R B)

set_option maxHeartbeats 10000000 in
-- The nested kernel and tensor equivalences require more elaboration time.
private noncomputable def determinantSubmodule_prodEquiv
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] :
    {e : TensorProduct R (determinantSubmodule (R := R) (M := A))
      (determinantSubmodule (R := R) (M := B)) ≃ₗ[R]
        determinantSubmodule (R := R) (M := A × B) //
      determinantSubmodule_prodEquiv_property e } := by
  classical
  let genA := Module.Finite.exists_fin (R := R) (M := A)
  let n := Classical.choose genA
  let s := Classical.choose (Classical.choose_spec genA)
  have hs : Submodule.span R (Set.range s) = ⊤ :=
    Classical.choose_spec (Classical.choose_spec genA)
  let genB := Module.Finite.exists_fin (R := R) (M := B)
  let m := Classical.choose genB
  let t := Classical.choose (Classical.choose_spec genB)
  have ht : Submodule.span R (Set.range t) = ⊤ :=
    Classical.choose_spec (Classical.choose_spec genB)
  let f := annMap (R := R) (M := A) s
  let g := annMapRight (R := R) (M := B) t
  let eA : determinantSubmodule (R := R) (M := A) ≃ₗ[R] LinearMap.ker f :=
    LinearEquiv.ofEq _ _ (determinantSubmodule_eq_ker_annMap s hs)
  let eB : determinantSubmodule (R := R) (M := B) ≃ₗ[R] LinearMap.ker g :=
    LinearEquiv.ofEq _ _ (determinantSubmodule_eq_ker_annMapRight t ht)
  letI : Module.Projective R (ExteriorAlgebra R B) := exteriorAlgebra_projective
  letI : Module.Flat R (ExteriorAlgebra R B) := Module.Flat.of_projective
  letI : Module.Projective R (⨁ _ : Fin m, ExteriorAlgebra R B) := inferInstance
  letI : Module.Projective R (Fin m → ExteriorAlgebra R B) :=
    Module.Projective.of_equiv'
      (DirectSum.linearEquivFunOnFintype R (Fin m) (fun _ => ExteriorAlgebra R B))
  letI : Module.Flat R (Fin m → ExteriorAlgebra R B) := Module.Flat.of_projective
  letI : Module.Projective R (determinantSubmodule (R := R) (M := A)) :=
    determinantSubmodule_projective
  letI : Module.Projective R (LinearMap.ker f) := Module.Projective.of_equiv' eA
  letI : Module.Flat R (LinearMap.ker f) := Module.Flat.of_projective
  let T := TensorProduct.congr eA eB
  let e := exteriorProdTensorEquiv (R := R) (A := A) (B := B)
  let F0 : TensorProduct R (determinantSubmodule (R := R) (M := A))
      (determinantSubmodule (R := R) (M := B)) →ₗ[R]
        ExteriorAlgebra R (A × B) :=
    e.symm.toLinearMap.comp
      ((TensorProduct.mapIncl f.ker g.ker).comp T.toLinearMap)
  let F : TensorProduct R (determinantSubmodule (R := R) (M := A))
      (determinantSubmodule (R := R) (M := B)) →ₗ[R]
        determinantSubmodule (R := R) (M := A × B) :=
    F0.codRestrict _ (by
      intro x
      apply (exteriorProdTensorEquiv_mem_joint_ker_iff s t hs ht (F0 x)).mp
      have hx : TensorProduct.mapIncl f.ker g.ker (T x) ∈
          LinearMap.ker (f.rTensor (ExteriorAlgebra R B)) ⊓
            LinearMap.ker (g.lTensor (ExteriorAlgebra R A)) := by
        rw [← tensorKerInf f g]
        exact ⟨T x, rfl⟩
      simpa [F0, e] using hx)
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      apply T.injective
      apply Module.Flat.tensorProduct_mapIncl_injective_of_left f.ker g.ker
      apply e.symm.injective
      exact congrArg Subtype.val hxy
    · intro y
      have hy : e y.1 ∈
          LinearMap.ker (f.rTensor (ExteriorAlgebra R B)) ⊓
            LinearMap.ker (g.lTensor (ExteriorAlgebra R A)) :=
        (exteriorProdTensorEquiv_mem_joint_ker_iff s t hs ht y.1).mpr y.2
      rw [← tensorKerInf f g] at hy
      obtain ⟨q, hq⟩ := hy
      obtain ⟨x, rfl⟩ := T.surjective q
      refine ⟨x, ?_⟩
      apply Subtype.ext
      apply e.injective
      simpa [F, F0, e] using hq
  refine ⟨LinearEquiv.ofBijective F hF, ?_⟩
  intro a b
  change e.symm (TensorProduct.mapIncl f.ker g.ker (T (a ⊗ₜ[R] b))) = _
  simp only [T, TensorProduct.congr_tmul, TensorProduct.mapIncl,
    TensorProduct.map_tmul]
  change e.symm ((a : ExteriorAlgebra R A) ⊗ₜ[R]
      (b : ExteriorAlgebra R B)) = _
  exact exteriorProdTensorEquiv_symm_tmul (R := R) (A := A) (B := B)
    (a : ExteriorAlgebra R A) (b : ExteriorAlgebra R B)

end

end ProjectiveDeterminant
