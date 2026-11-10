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
import all StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact.ProdDeterminant

/-!
# Determinants of short exact sequences of finite projective modules

Let `R` be a commutative ring. A short exact sequence `0 → M' → M → M'' → 0` of finite
projective `R`-modules induces a canonical isomorphism
`det M' ⊗ det M'' ≅ det M` of determinant lines. This isomorphism is natural in the sequence:
an isomorphism of short exact sequences carries one isomorphism to the other.

## Main definitions

* `ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact`: the isomorphism
  `det M' ⊗ det M'' ≅ det M` attached to a short exact sequence.

## Main results

* `ProjectiveDeterminant.determinantTensorDeterminantEquiv_naturality`: naturality along an
  isomorphism of short exact sequences.

## Implementation notes

Exactness is expressed by an injective first map, exactness at the middle term and a surjective
second map, rather than by a bundled short complex, so that the maps in the statements are the
ones the construction consumes.

## References

* [Stacks Project, Tag 0FJB](https://stacks.math.columbia.edu/tag/0FJB)
* [Stacks Project, Tag 0FJC](https://stacks.math.columbia.edu/tag/0FJC)
-/

namespace ProjectiveDeterminant

section

universe u v w x

open DirectSum
open scoped TensorProduct

/-- Functoriality of `ExteriorAlgebra.map`, stated pointwise. -/
private theorem exteriorMap_map_apply
    {R V W X : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup X] [Module R X] (f : V →ₗ[R] W) (g : W →ₗ[R] X)
    (z : ExteriorAlgebra R V) :
    ExteriorAlgebra.map g (ExteriorAlgebra.map f z) =
      ExteriorAlgebra.map (g.comp f) z := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

/-- The exterior algebra map of a linear equivalence is injective. -/
private theorem exteriorMap_injective_equiv
    {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) :
    Function.Injective (ExteriorAlgebra.map e.toLinearMap) :=
  ExteriorAlgebra.map_injective ⟨e.symm.toLinearMap, by ext m; simp⟩

private theorem determinantSubmodule_prodEquiv_tmul
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (a : determinantSubmodule (R := R) (M := A))
    (b : determinantSubmodule (R := R) (M := B)) :
    ((determinantSubmodule_prodEquiv (R := R) (A := A) (B := B)).1
        (a ⊗ₜ[R] b)).1 =
      ExteriorAlgebra.map (LinearMap.inl R A B) (a : ExteriorAlgebra R A) *
        ExteriorAlgebra.map (LinearMap.inr R A B) (b : ExteriorAlgebra R B) :=
  (determinantSubmodule_prodEquiv (R := R) (A := A) (B := B)).2 a b

private theorem exactEquivProd_map_f
    {R : Type u} [CommRing R]
    {M' : Type v} {M : Type w} {M'' : Type x}
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M''] [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (a : M') :
    exactEquivProd f g hf hfg hg (f a) = (a, 0) :=
  (exactEquivProdData f g hf hfg hg).2.1 a

private theorem exactEquivProd_snd
    {R : Type u} [CommRing R]
    {M' : Type v} {M : Type w} {M'' : Type x}
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M''] [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (m : M) :
    (exactEquivProd f g hf hfg hg m).2 = g m :=
  (exactEquivProdData f g hf hfg hg).2.2 m

private theorem exterior_mul_eq_mul_map_snd
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (z y : ExteriorAlgebra R (A × B))
    (hz : ∀ a : A, ExteriorAlgebra.ι R (a, 0) * z = 0) :
    z * y = z * ExteriorAlgebra.map (LinearMap.inr R A B)
      (ExteriorAlgebra.map (LinearMap.snd R A B) y) := by
  let j : ExteriorAlgebra R (A × B) →ₐ[R] ExteriorAlgebra R (A × B) :=
    ExteriorAlgebra.map ((LinearMap.inr R A B).comp (LinearMap.snd R A B))
  have hj (y : ExteriorAlgebra R (A × B)) :
      j y = ExteriorAlgebra.map (LinearMap.inr R A B)
        (ExteriorAlgebra.map (LinearMap.snd R A B) y) := by
    rw [exteriorMap_map_apply]
  rw [← hj]
  revert z
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
      intro z hz
      simp [j]
  | ι p =>
      intro z hz
      have hright : z * ExteriorAlgebra.ι R (p.1, 0) = 0 :=
        (mulLeft_ι_eq_zero_iff_mulRight (p.1, 0) z).1 (hz p.1)
      have hp : ExteriorAlgebra.ι R p =
          ExteriorAlgebra.ι R (p.1, 0) + ExteriorAlgebra.ι R (0, p.2) := by
        simpa using (map_add (ExteriorAlgebra.ι R) (p.1, 0) (0, p.2))
      rw [hp, mul_add, hright, zero_add]
      have hzero : ExteriorAlgebra.ι R ((0 : A), (0 : B)) = 0 := by
        simp
      simp [j, hzero]
  | mul a b ha hb =>
      intro z hz
      have hza : ∀ c : A, ExteriorAlgebra.ι R (c, 0) * (z * a) = 0 := by
        intro c
        rw [← mul_assoc, hz c, zero_mul]
      calc
        z * (a * b) = (z * a) * b := (mul_assoc z a b).symm
        _ = (z * a) * j b := hb (z * a) hza
        _ = (z * j a) * j b := by rw [ha z hz]
        _ = z * j (a * b) := by rw [map_mul, mul_assoc]
  | add a b ha hb =>
      intro z hz
      rw [map_add, mul_add, mul_add, ha z hz, hb z hz]

/-- A short exact sequence `0 → M' → M → M'' → 0` of finite projective modules has a canonical
determinant isomorphism. Its value on `x' ⊗ x''` is the wedge of the image of `x'` with any lift of
`x''` to the exterior algebra of `M`. -/
@[stacks 0FJB, sga "6 X 5.1" "affine case"]
public noncomputable def determinantTensorDeterminantEquiv_of_exact
    {R : Type u} [CommRing R]
    {M' : Type v} {M : Type w} {M'' : Type x}
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    { γ : TensorProduct R
          (↥(⨅ m : M', LinearMap.ker
            (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))))
          (↥(⨅ m : M'', LinearMap.ker
            (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)))) ≃ₗ[R]
        ↥(⨅ m : M, LinearMap.ker
          (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) //
      ∀ (x' : ↥(⨅ m : M', LinearMap.ker
            (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))))
        (x'' : ↥(⨅ m : M'', LinearMap.ker
            (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))))
        (y'' : ExteriorAlgebra R M),
        ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R M'') →
          ((γ (x' ⊗ₜ[R] x'') : ↥(⨅ m : M, LinearMap.ker
              (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)))) : ExteriorAlgebra R M) =
            ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * y'' }
    := by
  let e := exactEquivProd f g hf hfg hg
  let p := (determinantSubmodule_prodEquiv (R := R) (A := M') (B := M'')).1
  let d := determinantSubmodule_mapEquiv e
  have hef : e.toLinearMap.comp f = LinearMap.inl R M' M'' :=
    LinearMap.ext (exactEquivProd_map_f f g hf hfg hg)
  have heg : (LinearMap.snd R M' M'').comp e.toLinearMap = g := by
    ext m
    exact exactEquivProd_snd f g hf hfg hg m
  have hmapf (z : ExteriorAlgebra R M') :
      ExteriorAlgebra.map e.toLinearMap (ExteriorAlgebra.map f z) =
        ExteriorAlgebra.map (LinearMap.inl R M' M'') z := by
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hef]
  have hmapg (z : ExteriorAlgebra R M) :
      ExteriorAlgebra.map (LinearMap.snd R M' M'')
        (ExteriorAlgebra.map e.toLinearMap z) = ExteriorAlgebra.map g z := by
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, heg]
  have heinj : Function.Injective (ExteriorAlgebra.map e.toLinearMap) :=
    ExteriorAlgebra.map_injective ⟨e.symm.toLinearMap, by ext m; simp⟩
  refine ⟨p.trans d.symm, ?_⟩
  intro a b y hy
  apply heinj
  change ExteriorAlgebra.map e.toLinearMap
      ((d.symm (p (a ⊗ₜ[R] b)) : determinantSubmodule (R := R) (M := M)) :
        ExteriorAlgebra R M) =
    ExteriorAlgebra.map e.toLinearMap
      (ExteriorAlgebra.map f (a : ExteriorAlgebra R M') * y)
  have hd (z : determinantSubmodule (R := R) (M := M' × M'')) :
      ExteriorAlgebra.map e.toLinearMap
        ((d.symm z : determinantSubmodule (R := R) (M := M)) : ExteriorAlgebra R M) =
      (z : ExteriorAlgebra R (M' × M'')) := by
    have h := d.apply_symm_apply z
    exact congrArg Subtype.val h
  rw [hd, map_mul, hmapf, determinantSubmodule_prodEquiv_tmul]
  have hkill (m : M') :
      ExteriorAlgebra.ι R (m, 0) *
        ExteriorAlgebra.map (LinearMap.inl R M' M'') (a : ExteriorAlgebra R M') = 0 := by
    have ha : ExteriorAlgebra.ι R m * (a : ExteriorAlgebra R M') = 0 := by
      have ha' := a.2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at ha'
      exact ha' m
    have hm := congrArg (ExteriorAlgebra.map (LinearMap.inl R M' M'')) ha
    simpa using hm
  have hm := exterior_mul_eq_mul_map_snd
    (ExteriorAlgebra.map (LinearMap.inl R M' M'') (a : ExteriorAlgebra R M'))
    (ExteriorAlgebra.map e.toLinearMap y) hkill
  rw [hmapg, hy] at hm
  exact hm.symm

end

/-! ### Naturality -/

section

universe u v₁ v₂ v₃ w₁ w₂ w₃ v w

private abbrev DetSubmodule (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V]
    [Module R V] :=
  ⨅ x : V, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))

private theorem exteriorMap_commutes
    {R : Type u} [CommRing R] {A : Type v} {B : Type w}
    {C : Type v₁} {D : Type v₂}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D)
    (a : A ≃ₗ[R] C) (b : B ≃ₗ[R] D)
    (h : ∀ x : A, b (f x) = g (a x)) (z : ExteriorAlgebra R A) :
    ExteriorAlgebra.map b (ExteriorAlgebra.map f z) =
      ExteriorAlgebra.map g (ExteriorAlgebra.map a z) := by
  have hcomp : b.toLinearMap.comp f = g.comp a.toLinearMap := LinearMap.ext h
  rw [exteriorMap_map_apply f b.toLinearMap, exteriorMap_map_apply a.toLinearMap g, hcomp]

private theorem exteriorMap_mem_detSubmodule
    {R : Type u} [CommRing R] {V : Type v} {W : Type w}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) {z : ExteriorAlgebra R V} (hz : z ∈ DetSubmodule R V) :
    ExteriorAlgebra.map e z ∈ DetSubmodule R W := by
  simp only [DetSubmodule, Submodule.mem_iInf, LinearMap.mem_ker] at hz ⊢
  intro y
  have h := hz (e.symm y)
  have h' := congrArg (ExteriorAlgebra.map e.toLinearMap) h
  simpa [map_mul] using h'

private theorem exteriorMap_bijOn_detSubmodule
    {R : Type u} [CommRing R] {V : Type v} {W : Type w}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) :
    Set.BijOn (ExteriorAlgebra.map e) (DetSubmodule R V : Set (ExteriorAlgebra R V))
      (DetSubmodule R W : Set (ExteriorAlgebra R W)) := by
  apply Set.BijOn.mk
  · intro z hz
    exact exteriorMap_mem_detSubmodule e hz
  · exact fun z _ z' _ h => exteriorMap_injective_equiv e h
  · intro z hz
    refine ⟨ExteriorAlgebra.map e.symm.toLinearMap z,
      exteriorMap_mem_detSubmodule e.symm hz, ?_⟩
    have hright : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [exteriorMap_map_apply, hright, ExteriorAlgebra.map_id]
    rfl

private abbrev ExactDetData (R : Type u) [CommRing R]
    (A : Type v) (B : Type w) (C : Type v₁)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) :=
  {γ : TensorProduct R (DetSubmodule R A) (DetSubmodule R C) ≃ₗ[R] DetSubmodule R B //
    ∀ (x' : DetSubmodule R A) (x'' : DetSubmodule R C) (y'' : ExteriorAlgebra R B),
      ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R C) →
        ((γ (x' ⊗ₜ[R] x'') : DetSubmodule R B) : ExteriorAlgebra R B) =
          ExteriorAlgebra.map f (x' : ExteriorAlgebra R A) * y''}

private theorem naturality_of_detData
    {R : Type u} [CommRing R]
    {M' : Type v₁} {M : Type v₂} {M'' : Type v₃}
    {K' : Type w₁} {K : Type w₂} {K'' : Type w₃}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    [AddCommGroup K'] [Module R K'] [AddCommGroup K] [Module R K]
    [AddCommGroup K''] [Module R K'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (fK : K' →ₗ[R] K) (gK : K →ₗ[R] K'')
    (ΓM : ExactDetData R M' M M'' f g)
    (ΓK : ExactDetData R K' K K'' fK gK)
    (a : M' ≃ₗ[R] K') (b : M ≃ₗ[R] K) (c : M'' ≃ₗ[R] K'')
    (hab : ∀ x : M', b (f x) = fK (a x))
    (hbc : ∀ x : M, c (g x) = gK (b x)) (hg : Function.Surjective g) :
    ∀ (x' : DetSubmodule R M') (x'' : DetSubmodule R M'')
      (y' : DetSubmodule R K') (y'' : DetSubmodule R K''),
      ExteriorAlgebra.map a (x' : ExteriorAlgebra R M') = (y' : ExteriorAlgebra R K') →
      ExteriorAlgebra.map c (x'' : ExteriorAlgebra R M'') = (y'' : ExteriorAlgebra R K'') →
      ExteriorAlgebra.map b
        ((ΓM.val (x' ⊗ₜ[R] x'') : DetSubmodule R M) : ExteriorAlgebra R M) =
          ((ΓK.val (y' ⊗ₜ[R] y'') : DetSubmodule R K) : ExteriorAlgebra R K) := by
  intro x' x'' y' y'' h₁ h₂
  rcases ExteriorAlgebra.map_surjective_iff.mpr hg
      (x'' : ExteriorAlgebra R M'') with ⟨q, hq⟩
  have hcomp : gK.comp b.toLinearMap = c.toLinearMap.comp g := by
    ext m
    exact (hbc m).symm
  have hqK : ExteriorAlgebra.map gK (ExteriorAlgebra.map b q) =
      (y'' : ExteriorAlgebra R K'') := by
    rw [exteriorMap_map_apply, hcomp, ← exteriorMap_map_apply, hq, h₂]
  let qb : ExteriorAlgebra R K := ExteriorAlgebra.map b q
  have hqKb : ExteriorAlgebra.map gK qb = (y'' : ExteriorAlgebra R K'') := hqK
  let zm : ExteriorAlgebra R M :=
    (ΓM.val (x' ⊗ₜ[R] x'') : DetSubmodule R M)
  let zk : ExteriorAlgebra R K :=
    (ΓK.val (y' ⊗ₜ[R] y'') : DetSubmodule R K)
  have htopM : zm = ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * q :=
    ΓM.property x' x'' q hq
  have htopK : zk = ExteriorAlgebra.map fK (y' : ExteriorAlgebra R K') * qb :=
    ΓK.property y' y'' qb hqKb
  let xa : ExteriorAlgebra R K' := ExteriorAlgebra.map a (x' : ExteriorAlgebra R M')
  have hxa : xa = (y' : ExteriorAlgebra R K') := h₁
  have hmapf : ExteriorAlgebra.map b (ExteriorAlgebra.map f (x' : ExteriorAlgebra R M')) =
      ExteriorAlgebra.map fK (y' : ExteriorAlgebra R K') :=
    (exteriorMap_commutes f fK a b hab (x' : ExteriorAlgebra R M')).trans
      (congrArg (ExteriorAlgebra.map fK) hxa)
  let F : ExteriorAlgebra R M → ExteriorAlgebra R K :=
    fun z => (ExteriorAlgebra.map b.toLinearMap) z
  have step1 : F zm = F (ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * q) :=
    congrArg F htopM
  have step2 :
      F (ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * q) =
        F (ExteriorAlgebra.map f (x' : ExteriorAlgebra R M')) * F q :=
    map_mul (ExteriorAlgebra.map b.toLinearMap) _ _
  have step3 :
      F (ExteriorAlgebra.map f (x' : ExteriorAlgebra R M')) * F q =
        ExteriorAlgebra.map fK (y' : ExteriorAlgebra R K') * qb :=
    congrArg (fun z : ExteriorAlgebra R K => z * qb) hmapf
  have step4 : ExteriorAlgebra.map fK (y' : ExteriorAlgebra R K') * qb = zk :=
    htopK.symm
  change F zm = zk
  exact ((step1.trans step2).trans step3).trans step4

set_option maxHeartbeats 100000 in
-- Unfolding the dependent determinant-line `let`s requires a larger elaboration budget.
/-- The canonical determinant isomorphism of a short exact sequence of finite projective modules is
natural under an isomorphism of short exact sequences. -/
@[stacks 0FJC]
public theorem determinantTensorDeterminantEquiv_naturality
    {R : Type u} [CommRing R]
    {M' : Type v₁} {M : Type v₂} {M'' : Type v₃}
    {K' : Type w₁} {K : Type w₂} {K'' : Type w₃}
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M''] [Module.Projective R M'']
    [AddCommGroup K'] [Module R K'] [Module.Finite R K'] [Module.Projective R K']
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K]
    [AddCommGroup K''] [Module R K''] [Module.Finite R K''] [Module.Projective R K'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (fK : K' →ₗ[R] K) (gK : K →ₗ[R] K'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hfK : Function.Injective fK) (hfgK : Function.Exact fK gK)
    (hgK : Function.Surjective gK)
    (a : M' ≃ₗ[R] K') (b : M ≃ₗ[R] K) (c : M'' ≃ₗ[R] K'')
    (hab : ∀ x : M', b (f x) = fK (a x))
    (hbc : ∀ x : M, c (g x) = gK (b x)) :
    let D_M' : Submodule R (ExteriorAlgebra R M') :=
      ⨅ x : M', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let D_M : Submodule R (ExteriorAlgebra R M) :=
      ⨅ x : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let D_M'' : Submodule R (ExteriorAlgebra R M'') :=
      ⨅ x : M'', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let D_K' : Submodule R (ExteriorAlgebra R K') :=
      ⨅ x : K', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let D_K : Submodule R (ExteriorAlgebra R K) :=
      ⨅ x : K, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let D_K'' : Submodule R (ExteriorAlgebra R K'') :=
      ⨅ x : K'', LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R x))
    let γM := (determinantTensorDeterminantEquiv_of_exact f g hf hfg hg).val
    let γK := (determinantTensorDeterminantEquiv_of_exact fK gK hfK hfgK hgK).val
    Set.BijOn (ExteriorAlgebra.map a)
        (D_M' : Set (ExteriorAlgebra R M')) (D_K' : Set (ExteriorAlgebra R K')) ∧
      Set.BijOn (ExteriorAlgebra.map b)
        (D_M : Set (ExteriorAlgebra R M)) (D_K : Set (ExteriorAlgebra R K)) ∧
      Set.BijOn (ExteriorAlgebra.map c)
        (D_M'' : Set (ExteriorAlgebra R M'')) (D_K'' : Set (ExteriorAlgebra R K'')) ∧
      ∀ (x' : D_M') (x'' : D_M'') (y' : D_K') (y'' : D_K''),
        ExteriorAlgebra.map a (x' : ExteriorAlgebra R M') =
          (y' : ExteriorAlgebra R K') →
        ExteriorAlgebra.map c (x'' : ExteriorAlgebra R M'') =
          (y'' : ExteriorAlgebra R K'') →
        ExteriorAlgebra.map b
            ((γM (x' ⊗ₜ[R] x'') : D_M) : ExteriorAlgebra R M) =
          ((γK (y' ⊗ₜ[R] y'') : D_K) : ExteriorAlgebra R K)
    := by
  refine ⟨exteriorMap_bijOn_detSubmodule a,
    exteriorMap_bijOn_detSubmodule b,
    exteriorMap_bijOn_detSubmodule c, ?_⟩
  exact naturality_of_detData f g fK gK
    (determinantTensorDeterminantEquiv_of_exact f g hf hfg hg)
    (determinantTensorDeterminantEquiv_of_exact fK gK hfK hfgK hgK)
    a b c hab hbc hg

end

end ProjectiveDeterminant
