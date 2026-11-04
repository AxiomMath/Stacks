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
# Determinants of direct sums and the commutativity constraint

For a direct sum of finite projective modules, the canonical isomorphism
`det M' ⊗ det M'' ≅ det (M' × M'')` turns the commutativity constraint of the tensor product into
the map that switches the two summands, up to the sign given by the product of the local ranks.

## Main results

* `ProjectiveDeterminant.determinantTensorDeterminantEquiv_prodComm`: the sign rule for
  switching the two summands of a direct sum.

## Implementation notes

The sign is `(-1)` raised to the product of the local ranks, evaluated stratum by stratum.

## References

* [Stacks Project, Tag 0FJE](https://stacks.math.columbia.edu/tag/0FJE)
-/

namespace ProjectiveDeterminant

/-! ### Direct sums and the commutativity constraint -/

section

universe u v w

open scoped TensorProduct

private theorem det_neg_id_isUnit
    {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    IsUnit (ProjectiveDeterminant.det
      (-(LinearMap.id : M →ₗ[R] M))) := by
  let f : M →ₗ[R] M := -LinearMap.id
  have hff : f.comp f = LinearMap.id := by
    ext x
    simp [f]
  have hdet : ProjectiveDeterminant.det f * ProjectiveDeterminant.det f = 1 := by
    rw [← ProjectiveDeterminant.det_comp, hff]
    exact ((Classical.choose_spec (ProjectiveDeterminant.existsUnique_scalar
      (M := M) (ProjectiveDeterminant.map (M := M) (N := M)
        (fun _ => rfl) (LinearMap.id : M →ₗ[R] M)))).2 1 (by
          rw [ProjectiveDeterminant.map_id]
          simp)).symm
  exact isUnit_iff_exists_inv.mpr ⟨_, hdet⟩

private theorem map_neg_id_of_mem_fixedDegree
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : ExteriorAlgebra R M) (hx : x ∈ ⋀[R]^n M) :
    ExteriorAlgebra.map (-(LinearMap.id : M →ₗ[R] M)) x = (-1 : R) ^ n • x := by
  rw [← (Submodule.ext_iff.mp (ExteriorAlgebra.ιMulti_span_fixedDegree R n))] at hx
  refine Submodule.span_induction (p := fun x _ =>
    ExteriorAlgebra.map (-(LinearMap.id : M →ₗ[R] M)) x = (-1 : R) ^ n • x)
      ?_ (by simp) (by simp +contextual) (by
        intro a x hx ih
        rw [map_smul, ih, smul_comm]) hx
  rintro _ ⟨m, rfl⟩
  rw [ExteriorAlgebra.map_apply_ιMulti]
  show ExteriorAlgebra.ιMulti R n (fun i => -m i) = _
  have hneg (n : ℕ) (m : Fin n → M) :
      ExteriorAlgebra.ιMulti R n (fun i => -m i) =
        (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n m := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        show Matrix.vecTail (fun i => -m i) = fun i => -(Matrix.vecTail m i) by rfl,
        ih (Matrix.vecTail m)]
      simp [pow_succ]
  exact hneg n m

private theorem det_neg_id_smul_component
    {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ProjectiveDeterminant.component (R := R) (M := M) n) :
    ProjectiveDeterminant.det (-(LinearMap.id : M →ₗ[R] M)) • x =
      (-1 : R) ^ n • x := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hmap := congrArg Subtype.val (LinearMap.congr_fun
    (Classical.choose_spec (ProjectiveDeterminant.existsUnique_scalar
      (M := M) (ProjectiveDeterminant.map (M := M) (N := M) (fun _ => rfl)
        (-(LinearMap.id : M →ₗ[R] M))))).1
    ⟨_, ProjectiveDeterminant.component_le_submodule n
      (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)⟩)
  change ExteriorAlgebra.map (-(LinearMap.id : M →ₗ[R] M))
      (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n • y) =
    ProjectiveDeterminant.det (-(LinearMap.id : M →ₗ[R] M)) •
      (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n • y) at hmap
  rw [map_smul, map_neg_id_of_mem_fixedDegree n y hy] at hmap
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_comm] using hmap.symm

private theorem rankIdempotent_smul_self
    {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ProjectiveDeterminant.component (R := R) (M := M) n) :
    ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n • x = x := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  show (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n : R) •
    ((ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n : R) • y) =
      (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n : R) • y
  rw [← mul_smul, (ProjectiveDeterminant.rankIdempotent_spec
    (R := R) (M := M) n).1]

/-- An element of the `n`-th component of the determinant lies in the `n`-th exterior power. -/
private theorem mem_exteriorPower_of_mem_component
    {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ProjectiveDeterminant.component (R := R) (M := M) n) : x ∈ ⋀[R]^n M := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.smul_mem _ _ hy

private theorem rankProduct_mul_rankIdempotent_eq_zero
    {R : Type u} [CommRing R]
    (M' : Type v) (M'' : Type w)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    {i j k : ℕ} (hk : k ≠ i * j) :
    (ProjectiveDeterminant.rankIdempotent (R := R) (M := M') i *
        ProjectiveDeterminant.rankIdempotent (R := R) (M := M'') j) *
      ProjectiveDeterminant.rankIdempotent
        (R := R) (M := TensorProduct R M' M'') k = 0 := by
  let e := ProjectiveDeterminant.rankIdempotent (R := R) (M := M') i
  let f := ProjectiveDeterminant.rankIdempotent (R := R) (M := M'') j
  let g := ProjectiveDeterminant.rankIdempotent
    (R := R) (M := TensorProduct R M' M'') k
  have hopen : PrimeSpectrum.basicOpen ((e * f) * g) = ⊥ := by
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_mul]
    apply TopologicalSpace.Opens.ext
    show ((PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) ∩
      PrimeSpectrum.basicOpen f) ∩ PrimeSpectrum.basicOpen g = ∅
    rw [← (ProjectiveDeterminant.rankIdempotent_spec
      (R := R) (M := M') i).2,
      ← (ProjectiveDeterminant.rankIdempotent_spec
        (R := R) (M := M'') j).2,
      ← (ProjectiveDeterminant.rankIdempotent_spec
        (R := R) (M := TensorProduct R M' M'') k).2]
    ext p
    simp only [ProjectiveDeterminant.rankLocus, Set.mem_inter_iff,
      Set.mem_empty_iff_false]
    constructor
    · rintro ⟨⟨hi, hj⟩, hkp⟩
      apply hk
      rw [← hkp, Module.rankAtStalk_tensorProduct]
      exact congrArg₂ (· * ·) hi hj
    · exact False.elim
  have hnil : IsNilpotent ((e * f) * g) :=
    (PrimeSpectrum.basicOpen_eq_bot_iff _).mp hopen
  have hid : IsIdempotentElem ((e * f) * g) := by
    have he := (ProjectiveDeterminant.rankIdempotent_spec
      (R := R) (M := M') i).1
    have hf := (ProjectiveDeterminant.rankIdempotent_spec
      (R := R) (M := M'') j).1
    have hg := (ProjectiveDeterminant.rankIdempotent_spec
      (R := R) (M := TensorProduct R M' M'') k).1
    dsimp [e, f, g]
    calc
      ((e * f) * g) * ((e * f) * g) = (e * e) * (f * f) * (g * g) := by ring
      _ = (e * f) * g := by rw [he, hf, hg]
  exact hid.eq_zero_of_isNilpotent hnil

private theorem rankProduct_mul_det_neg_id
    {R : Type u} [CommRing R]
    (M' : Type v) (M'' : Type w)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    (i j : ℕ) :
    let e := ProjectiveDeterminant.rankIdempotent (R := R) (M := M') i *
      ProjectiveDeterminant.rankIdempotent (R := R) (M := M'') j
    e * ProjectiveDeterminant.det
        (-(LinearMap.id : TensorProduct R M' M'' →ₗ[R] TensorProduct R M' M'')) =
      e * (-1 : R) ^ (i * j) := by
  dsimp only
  let T := TensorProduct R M' M''
  let e := ProjectiveDeterminant.rankIdempotent (R := R) (M := M') i *
    ProjectiveDeterminant.rankIdempotent (R := R) (M := M'') j
  let d := ProjectiveDeterminant.det (-(LinearMap.id : T →ₗ[R] T))
  let := ProjectiveDeterminant.invertible (R := R) (M := T)
  apply (Module.Invertible.toModuleEnd_bijective R
    (ProjectiveDeterminant.module (R := R) (M := T))).1
  apply LinearMap.ext
  intro z
  show (e * d) • z = (e * (-1 : R) ^ (i * j)) • z
  apply Subtype.ext
  rcases z with ⟨z, hz⟩
  show (e * d) • z = (e * (-1 : R) ^ (i * j)) • z
  rw [mul_smul e d, mul_smul e ((-1 : R) ^ (i * j))]
  change z ∈ ⨆ k, ProjectiveDeterminant.component (R := R) (M := T) k at hz
  apply Submodule.iSup_induction
    (fun k => ProjectiveDeterminant.component (R := R) (M := T) k) hz
    (motive := fun z => e • (d • z) = e • (((-1 : R) ^ (i * j)) • z))
  · intro k z hz
    by_cases hk : k = i * j
    · subst k
      rw [det_neg_id_smul_component (i * j) z hz]
    · have hzero : e • z = 0 := by
        rw [← rankIdempotent_smul_self hz, ← mul_smul,
          rankProduct_mul_rankIdempotent_eq_zero M' M'' hk, zero_smul]
      rw [smul_comm e d, smul_comm e ((-1 : R) ^ (i * j)), hzero, smul_zero, smul_zero]
  · simp
  · intro x y hx hy
    simp only [smul_add, hx, hy]

/-- Switching the summands of a direct sum, after mapping the exterior algebra of `N` into it. -/
private theorem map_prodComm_map
    {R : Type u} [CommRing R] {M' : Type v} {M'' : Type w} {N : Type*}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup N] [Module R N] (f : N →ₗ[R] M' × M'') (g : N →ₗ[R] M'' × M')
    (h : (LinearEquiv.prodComm R M' M'').toLinearMap ∘ₗ f = g) (z : ExteriorAlgebra R N) :
    ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
      (ExteriorAlgebra.map f z) = ExteriorAlgebra.map g z := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h]

private theorem koszul_switch
    {R : Type u} [CommRing R]
    (M' : Type v) (M'' : Type w)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    (a : ProjectiveDeterminant.module (R := R) (M := M'))
    (b : ProjectiveDeterminant.module (R := R) (M := M'')) :
    ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'')
        (ExteriorAlgebra.map (LinearMap.inl R M' M'') a.1 *
          ExteriorAlgebra.map (LinearMap.inr R M' M'') b.1) =
      ProjectiveDeterminant.det
          (-(LinearMap.id : TensorProduct R M' M'' →ₗ[R] TensorProduct R M' M'')) •
        (ExteriorAlgebra.map (LinearMap.inl R M'' M') b.1 *
          ExteriorAlgebra.map (LinearMap.inr R M'' M') a.1) := by
  let d := ProjectiveDeterminant.det
    (-(LinearMap.id : TensorProduct R M' M'' →ₗ[R] TensorProduct R M' M''))
  have hgoal (x : ExteriorAlgebra R M')
      (hx : x ∈ ProjectiveDeterminant.submodule (R := R) (M := M'))
      (y : ExteriorAlgebra R M'')
      (hy : y ∈ ProjectiveDeterminant.submodule (R := R) (M := M'')) :
      ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'')
          (ExteriorAlgebra.map (LinearMap.inl R M' M'') x *
            ExteriorAlgebra.map (LinearMap.inr R M' M'') y) =
        d • (ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
          ExteriorAlgebra.map (LinearMap.inr R M'' M') x) := by
    let P := fun x : ExteriorAlgebra R M' => ∀ y : ExteriorAlgebra R M'',
      y ∈ ProjectiveDeterminant.submodule (R := R) (M := M'') →
      ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
          (ExteriorAlgebra.map (LinearMap.inl R M' M'') x *
            ExteriorAlgebra.map (LinearMap.inr R M' M'') y) =
        d • (ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
          ExteriorAlgebra.map (LinearMap.inr R M'' M') x)
    refine (Submodule.iSup_induction
      (fun i => ProjectiveDeterminant.component (R := R) (M := M') i)
      (show x ∈ ⨆ i, ProjectiveDeterminant.component (R := R) (M := M') i from hx)
      (motive := P) ?_ ?_ ?_) y hy
    · intro i x hxi y hy
      let Q := fun y : ExteriorAlgebra R M'' =>
        ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
            (ExteriorAlgebra.map (LinearMap.inl R M' M'') x *
              ExteriorAlgebra.map (LinearMap.inr R M' M'') y) =
          d • (ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
            ExteriorAlgebra.map (LinearMap.inr R M'' M') x)
      refine Submodule.iSup_induction
        (fun j => ProjectiveDeterminant.component (R := R) (M := M'') j)
        (show y ∈ ⨆ j, ProjectiveDeterminant.component (R := R) (M := M'') j from hy)
        (motive := Q) ?_ ?_ ?_
      · intro j y hyj
        let ei := ProjectiveDeterminant.rankIdempotent (R := R) (M := M') i
        let ej := ProjectiveDeterminant.rankIdempotent (R := R) (M := M'') j
        have hxi' : ei • x = x := rankIdempotent_smul_self hxi
        have hyj' : ej • y = y := rankIdempotent_smul_self hyj
        have hswap := congrArg
          (ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap)
          (ExteriorAlgebra.map_inl_inr_anticomm (R := R) i j
            (⟨x, mem_exteriorPower_of_mem_component hxi⟩ : ⋀[R]^i M')
            (⟨y, mem_exteriorPower_of_mem_component hyj⟩ : ⋀[R]^j M''))
        have hsign :
            ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
                (ExteriorAlgebra.map (LinearMap.inl R M' M'') x *
                  ExteriorAlgebra.map (LinearMap.inr R M' M'') y) =
              (-1 : R) ^ (j * i) •
                (ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
                  ExteriorAlgebra.map (LinearMap.inr R M'' M') x) := by
          have h₁ := map_prodComm_map (LinearMap.inl R M' M'') (LinearMap.inr R M'' M') rfl x
          have h₂ := map_prodComm_map (LinearMap.inr R M' M'') (LinearMap.inl R M'' M') rfl y
          have h₃ : ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
              (ExteriorAlgebra.map (LinearMap.inr R M' M'') y *
                ExteriorAlgebra.map (LinearMap.inl R M' M'') x) =
              ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
                ExteriorAlgebra.map (LinearMap.inr R M'' M') x := by
            rw [map_mul, h₂, h₁]
          simpa [map_mul, h₁, h₂, h₃, Algebra.smul_def] using hswap
        dsimp [Q]
        rw [hsign, Nat.mul_comm j i]
        show (-1 : R) ^ (i * j) • _ = d • _
        let q := ExteriorAlgebra.map (LinearMap.inl R M'' M') y *
          ExteriorAlgebra.map (LinearMap.inr R M'' M') x
        have hq : (ei * ej) • q = q := by
          have hh := congrArg₂ (· * ·)
            (congrArg (ExteriorAlgebra.map (LinearMap.inl R M'' M')) hyj')
            (congrArg (ExteriorAlgebra.map (LinearMap.inr R M'' M')) hxi')
          simpa [q, map_smul, mul_smul, smul_mul_assoc, mul_smul_comm,
            mul_comm, mul_left_comm] using hh
        have hs := rankProduct_mul_det_neg_id (R := R) M' M'' i j
        calc
          (-1 : R) ^ (i * j) • q = ((ei * ej) * (-1 : R) ^ (i * j)) • q := by
            rw [mul_smul, smul_comm (ei * ej), hq]
          _ = ((ei * ej) * d) • q := by rw [hs]
          _ = d • q := by rw [mul_smul, smul_comm (ei * ej) d, hq]
      · simp only [Q, map_zero, zero_mul, mul_zero, smul_zero]
      · intro y y' hy hy'
        dsimp [Q] at hy hy' ⊢
        simp only [map_add, add_mul, mul_add, smul_add, hy, hy']
    · simp only [P, map_zero, zero_mul, mul_zero, smul_zero, implies_true]
    · intro x x' hx hx'
      intro y hy
      specialize hx y hy
      specialize hx' y hy
      show ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'').toLinearMap
          (ExteriorAlgebra.map (LinearMap.inl R M' M'') (x + x') *
            ExteriorAlgebra.map (LinearMap.inr R M' M'') y) = _
      simp only [map_add, add_mul, mul_add, smul_add, hx, hx']
  exact hgoal a.1 a.2 b.1 b.2

/-- The canonical isomorphism for a direct sum sends `a ⊗ b` to the wedge of their images. -/
private theorem coe_determinantTensorDeterminantEquiv_prod_tmul
    {R : Type u} [CommRing R] (M' : Type v) (M'' : Type w)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    (a : (⨅ m : M', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) :
      Submodule R (ExteriorAlgebra R M')))
    (b : (⨅ m : M'', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) :
      Submodule R (ExteriorAlgebra R M''))) :
    ((determinantTensorDeterminantEquiv_of_exact
      (LinearMap.inl R M' M'') (LinearMap.snd R M' M'')
      LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective).val (a ⊗ₜ[R] b) :
        ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (LinearMap.inl R M' M'') a.1 *
        ExteriorAlgebra.map (LinearMap.inr R M' M'') b.1 :=
  (determinantTensorDeterminantEquiv_of_exact
    (LinearMap.inl R M' M'') (LinearMap.snd R M' M'')
    LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective).property
    a b (ExteriorAlgebra.map (LinearMap.inr R M' M'') b.1) (by
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      simp)

/-- Switching the summands in a direct sum is compatible with the canonical isomorphism from the
tensor product of their determinant lines, up to the determinant of minus the identity on the
tensor product of the summands. -/
@[stacks 0FJE]
public theorem determinantTensorDeterminantEquiv_prodComm
    {R : Type u} [CommRing R]
    (M' : Type v) (M'' : Type w)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M''] :
    let D' : Submodule R (ExteriorAlgebra R M') :=
      ⨅ m : M', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))
    let D'' : Submodule R (ExteriorAlgebra R M'') :=
      ⨅ m : M'', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))
    let D'_prod_D'' : Submodule R (ExteriorAlgebra R (M' × M'')) :=
      ⨅ m : M' × M'', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))
    let D''_prod_D' : Submodule R (ExteriorAlgebra R (M'' × M')) :=
      ⨅ m : M'' × M', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))
    let γ' := (determinantTensorDeterminantEquiv_of_exact
      (LinearMap.inl R M' M'') (LinearMap.snd R M' M'')
      LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective).val
    let γ'' := (determinantTensorDeterminantEquiv_of_exact
      (LinearMap.inl R M'' M') (LinearMap.snd R M'' M')
      LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective).val
    ∃ ε : Rˣ,
      (ε : R) = ProjectiveDeterminant.det
        (-(LinearMap.id : TensorProduct R M' M'' →ₗ[R] TensorProduct R M' M'')) ∧
      ∀ x : TensorProduct R D' D'',
        ExteriorAlgebra.map (LinearEquiv.prodComm R M' M'')
            ((γ' x : D'_prod_D'') : ExteriorAlgebra R (M' × M'')) =
          ((γ'' ((ε : R) • TensorProduct.comm R D' D'' x) : D''_prod_D') :
            ExteriorAlgebra R (M'' × M'))
    := by
  dsimp only
  let d := ProjectiveDeterminant.det
    (-(LinearMap.id : TensorProduct R M' M'' →ₗ[R] TensorProduct R M' M''))
  let ε : Rˣ := (det_neg_id_isUnit (R := R) (M := TensorProduct R M' M'')).unit
  refine ⟨ε, rfl, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      let ha : ProjectiveDeterminant.module (R := R) (M := M') :=
        ⟨a.1, by rw [determinant_submodule_eq_annihilator]; exact a.2⟩
      let hb : ProjectiveDeterminant.module (R := R) (M := M'') :=
        ⟨b.1, by rw [determinant_submodule_eq_annihilator]; exact b.2⟩
      rw [TensorProduct.comm_tmul]
      rw [coe_determinantTensorDeterminantEquiv_prod_tmul M' M'' a b]
      have heq := congrArg Subtype.val (map_smul
        (determinantTensorDeterminantEquiv_of_exact
          (LinearMap.inl R M'' M') (LinearMap.snd R M'' M')
          LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective).val
        (ε : R) (b ⊗ₜ[R] a))
      rw [heq]
      rw [SetLike.val_smul]
      rw [coe_determinantTensorDeterminantEquiv_prod_tmul M'' M' b a]
      have hε : (ε : R) = d := rfl
      rw [hε]
      simpa only [map_mul] using koszul_switch M' M'' ha hb
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, smul_add, hx, hy]

end

end ProjectiveDeterminant
