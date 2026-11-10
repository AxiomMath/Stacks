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
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact.Construction

/-!
# Determinants of short exact sequences and two-step filtrations

The canonical isomorphism `det M' ⊗ det M'' ≅ det M` of a short exact sequence of finite projective
modules is compatible with a two-step filtration `K ⊆ L ⊆ M`: both ways of cutting `M` give the
same map out of `det K ⊗ det (L / K) ⊗ det (M / L)`.

## Main results

* `ProjectiveDeterminant.determinantEquiv_filtration`: compatibility with a two-step
  filtration.

## References

* [Stacks Project, Tag 0FJD](https://stacks.math.columbia.edu/tag/0FJD)
-/

namespace ProjectiveDeterminant

/-! ### Compatibility with a two-step filtration -/

section

universe u v

private theorem projective_of_exact
    {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Projective R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) : Module.Projective R B := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : A × C →ₗ[R] B := f.coprod s
  have hgf (a : A) : g (f a) = 0 := (hfg (f a)).2 ⟨a, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨a, c⟩ ⟨a', c'⟩ hac
      have hc : c = c' := by
        apply_fun g at hac
        simp only [e, LinearMap.coprod_apply, map_add, hgf, zero_add] at hac
        simpa only [← LinearMap.comp_apply, hs, LinearMap.id_apply] using hac
      subst c'
      simp only [e, LinearMap.coprod_apply, add_left_inj] at hac
      exact Prod.ext (hf hac) rfl
    · intro b
      have hb : g (b - s (g b)) = 0 := by
        rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
      obtain ⟨a, ha⟩ := (hfg _).1 hb
      refine ⟨(a, g b), ?_⟩
      simp only [e, LinearMap.coprod_apply]
      rw [ha]
      abel
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective e he)

/-- `K ⊆ L` and the quotient `L → L / K` form a short exact sequence. -/
private theorem exact_inclusion_mkQ_submoduleOf {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (Submodule.inclusion hKL) (K.submoduleOf L).mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
  ext x
  simp [Submodule.submoduleOf]

/-- Applying `ExteriorAlgebra.map` to a composite of linear maps. -/
private theorem exteriorAlgebra_map_map {R A B C : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (x : ExteriorAlgebra R A) :
    ExteriorAlgebra.map g (ExteriorAlgebra.map f x) = ExteriorAlgebra.map (g ∘ₗ f) x := by
  rw [← ExteriorAlgebra.map_comp_map]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the nested determinant-line submodules requires additional heartbeats.
/-- For finite projective successive quotients of a filtration `K ≤ L ≤ M`, combining the canonical
determinant equivalences first across `K ≤ L` or first across the induced sequence
`L / K → M / K → M / L` gives the same equivalence to the determinant line of `M`. -/
@[stacks 0FJD]
public theorem determinantEquiv_filtration
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R K] [Module.Projective R K]
    [Module.Finite R (L ⧸ K.submoduleOf L)]
    [Module.Projective R (L ⧸ K.submoduleOf L)]
    [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)] :
    let iQ : (L ⧸ K.submoduleOf L) →ₗ[R] (M ⧸ K) :=
      (K.submoduleOf L).mapQ K L.subtype (by
        intro x hx
        exact hx)
    let pQ : (M ⧸ K) →ₗ[R] (M ⧸ L) :=
      K.mapQ L LinearMap.id (by simpa using hKL)
    ∃ hLfin : Module.Finite R L,
      ∃ hLproj : Module.Projective R L,
        ∃ hMKfin : Module.Finite R (M ⧸ K),
          ∃ hMKproj : Module.Projective R (M ⧸ K),
            ∃ hMfin : Module.Finite R M,
              ∃ hMproj : Module.Projective R M,
                let _ : Module.Finite R L := hLfin
                let _ : Module.Projective R L := hLproj
                let _ : Module.Finite R (M ⧸ K) := hMKfin
                let _ : Module.Projective R (M ⧸ K) := hMKproj
                let _ : Module.Finite R M := hMfin
                let _ : Module.Projective R M := hMproj
                let hiQ : Function.Injective iQ
    := by
                  intro x y hxy
                  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (K.submoduleOf L) x
                  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (K.submoduleOf L) y
                  change K.mkQ x.1 = K.mkQ y.1 at hxy
                  change Submodule.Quotient.mk x = Submodule.Quotient.mk y
                  rw [Submodule.Quotient.eq]
                  exact (Submodule.Quotient.eq K).mp hxy
                let hpQ : Function.Surjective pQ := by
                  intro x
                  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L x
                  exact ⟨K.mkQ x, rfl⟩
                let hexQ : Function.Exact iQ pQ := by
                  intro x
                  constructor
                  · intro hx
                    induction x using Submodule.Quotient.induction_on with
                    | _ x =>
                      have hxL : x ∈ L := by
                        simpa [pQ] using hx
                      exact ⟨(K.submoduleOf L).mkQ ⟨x, hxL⟩, rfl⟩
                  · rintro ⟨y, rfl⟩
                    induction y using Submodule.Quotient.induction_on with
                    | _ y =>
                      change L.mkQ y.1 = 0
                      change Submodule.Quotient.mk y.1 = Submodule.Quotient.mk 0
                      exact (Submodule.Quotient.eq L).mpr (by simpa only [sub_zero] using y.2)
                let γKL := determinantTensorDeterminantEquiv_of_exact
                  (Submodule.inclusion hKL) (K.submoduleOf L).mkQ
                  (Submodule.inclusion_injective hKL)
                  (by
                    rw [LinearMap.exact_iff, Submodule.ker_mkQ,
                      Submodule.range_inclusion]
                    rfl)
                  (Submodule.mkQ_surjective _)
                let γLM := determinantTensorDeterminantEquiv_of_exact
                  L.subtype L.mkQ L.subtype_injective
                  (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
                let γKM := determinantTensorDeterminantEquiv_of_exact
                  K.subtype K.mkQ K.subtype_injective
                  (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
                let γQ := determinantTensorDeterminantEquiv_of_exact
                  iQ pQ hiQ hexQ hpQ
                γKL.1.rTensor _ ≪≫ₗ γLM.1 =
                  TensorProduct.assoc R _ _ _ ≪≫ₗ γQ.1.lTensor _ ≪≫ₗ γKM.1 := by
  dsimp only
  have hexKL := exact_inclusion_mkQ_submoduleOf K L hKL
  let : Module.Finite R L := Module.Finite.of_exact hexKL (Submodule.mkQ_surjective _)
  let : Module.Projective R L := projective_of_exact
    (Submodule.inclusion hKL) (K.submoduleOf L).mkQ
    (Submodule.inclusion_injective hKL) hexKL (Submodule.mkQ_surjective _)
  let pQ : (M ⧸ K) →ₗ[R] (M ⧸ L) :=
    K.mapQ L LinearMap.id (by simpa using hKL)
  have hpQ : Function.Surjective pQ := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L x
    exact ⟨K.mkQ x, rfl⟩
  let iQ : (L ⧸ K.submoduleOf L) →ₗ[R] (M ⧸ K) :=
    (K.submoduleOf L).mapQ K L.subtype (by intro x hx; exact hx)
  have hiQ : Function.Injective iQ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (K.submoduleOf L) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (K.submoduleOf L) y
    change K.mkQ x.1 = K.mkQ y.1 at hxy
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq]
    exact (Submodule.Quotient.eq K).mp hxy
  have hexQ : Function.Exact iQ pQ := by
    intro x
    constructor
    · intro hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        have hxL : x ∈ L := by simpa [pQ] using hx
        exact ⟨(K.submoduleOf L).mkQ ⟨x, hxL⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change L.mkQ y.1 = 0
        change Submodule.Quotient.mk y.1 = Submodule.Quotient.mk 0
        exact (Submodule.Quotient.eq L).mpr (by simpa only [sub_zero] using y.2)
  let : Module.Finite R (M ⧸ K) := Module.Finite.of_exact hexQ hpQ
  let : Module.Projective R (M ⧸ K) := projective_of_exact iQ pQ hiQ hexQ hpQ
  let : Module.Finite R M := Module.Finite.of_submodule_quotient L
  let : Module.Projective R M := projective_of_exact L.subtype L.mkQ
    L.subtype_injective (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  apply LinearEquiv.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using
      (congrArg₂ (fun a b => a + b) hx hy)
  | tmul xy z =>
    induction xy using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, TensorProduct.add_tmul] using
        (congrArg₂ (fun a b => a + b) hx hy)
    | tmul x y =>
      simp only [LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
        LinearEquiv.lTensor_tmul, TensorProduct.assoc_tmul]
      let γKL := determinantTensorDeterminantEquiv_of_exact
        (Submodule.inclusion hKL) (K.submoduleOf L).mkQ
        (Submodule.inclusion_injective hKL)
        hexKL (Submodule.mkQ_surjective _)
      let γLM := determinantTensorDeterminantEquiv_of_exact
        L.subtype L.mkQ L.subtype_injective
        (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
      let γKM := determinantTensorDeterminantEquiv_of_exact
        K.subtype K.mkQ K.subtype_injective
        (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
      let γQ := determinantTensorDeterminantEquiv_of_exact iQ pQ hiQ hexQ hpQ
      change γLM.1 (γKL.1 (x ⊗ₜ[R] y) ⊗ₜ[R] z) =
        γKM.1 (x ⊗ₜ[R] γQ.1 (y ⊗ₜ[R] z))
      obtain ⟨y₀, hy₀⟩ := (ExteriorAlgebra.map_surjective_iff.mpr
        (Submodule.mkQ_surjective (K.submoduleOf L))) (y : ExteriorAlgebra R _)
      obtain ⟨z₀, hz₀⟩ := (ExteriorAlgebra.map_surjective_iff.mpr
        (Submodule.mkQ_surjective L)) (z : ExteriorAlgebra R _)
      apply Subtype.ext
      rw [γLM.2 (γKL.1 (x ⊗ₜ[R] y)) z z₀ hz₀]
      rw [γKL.2 x y y₀ hy₀]
      have hpz : ExteriorAlgebra.map pQ (ExteriorAlgebra.map K.mkQ z₀) =
          (z : ExteriorAlgebra R (M ⧸ L)) := by
        rw [exteriorAlgebra_map_map]
        change ExteriorAlgebra.map L.mkQ z₀ = _
        exact hz₀
      have hQ := γQ.2 y z (ExteriorAlgebra.map K.mkQ z₀) hpz
      have hiqy : ExteriorAlgebra.map iQ (y : ExteriorAlgebra R _) =
          ExteriorAlgebra.map K.mkQ (ExteriorAlgebra.map L.subtype y₀) := by
        rw [← hy₀]
        rw [exteriorAlgebra_map_map, exteriorAlgebra_map_map]
        congr 2
      have hlift : ExteriorAlgebra.map K.mkQ
          (ExteriorAlgebra.map L.subtype y₀ * z₀) =
          ((γQ.1 (y ⊗ₜ[R] z) : _) : ExteriorAlgebra R (M ⧸ K)) := by
        rw [map_mul, ← hiqy, ← hQ]
      rw [γKM.2 x (γQ.1 (y ⊗ₜ[R] z))
        (ExteriorAlgebra.map L.subtype y₀ * z₀) hlift]
      rw [map_mul, mul_assoc]
      congr 1
      rw [exteriorAlgebra_map_map]
      congr 2

end

end ProjectiveDeterminant
