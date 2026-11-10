module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Discriminant.LocalAnnihilation

/-!
# Base change of a relative dualizing module is independent of the factorization

The relative dualizing module of a quasi-finite map `A → B` is computed from a chosen
finite-open factorization, and the base change map to the dualizing module over `A₁ ⊗[A] B`
is computed from the base change of that factorization. This file shows that the square
formed by two such choices and the canonical comparisons between the dualizing modules
commutes, so the base change map is intrinsic.

The proof reduces to the case of a refinement `F → H` of factorizations. There the comparison
map is pinned down by its effect on pure tensors coming from the larger intermediate algebra,
and the identity to be checked is local on `Spec` of the target: the difference of the two
sides is killed by an element outside every prime, hence vanishes.

## Main results

* `Stacks.Discriminant.dualizingModule.baseChange_congr`: the base change maps attached to two
  finite-open factorizations agree after the canonical comparison isomorphisms.

## Implementation notes

The local statement needs a uniform exponent annihilating the whole kernel of the
base-changed intermediate algebra, not just one element of it; this is where Noetherianity of
the base of the scalar extension enters.

## References

* [Stacks Project, Tag 0BVC](https://stacks.math.columbia.edu/tag/0BVC)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

/-- The structure map of a base-changed finite-open factorization sends a pure tensor to the
pure tensor of its image. -/
private theorem finiteOpen_baseChange_algebraMap_tmul
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (A₁ : Type y) [CommRing A₁] [Algebra A A₁]
    (a : A₁) (c : F.middle) :
    algebraMap (FiniteOpenFactorization.baseChange F A₁).middle
        (A₁ ⊗[A] B) (a ⊗ₜ[A] c) =
      a ⊗ₜ[A] algebraMap F.middle B c := by
  let : CommRing F.middle := F.commRingMiddle
  let : Algebra A F.middle := F.algebraMiddle
  let : Algebra F.middle B := F.algebraTarget
  let : IsScalarTower A F.middle B := F.scalarTower
  change (Algebra.TensorProduct.map (AlgHom.id A A₁)
    (IsScalarTower.toAlgHom A F.middle B)) (a ⊗ₜ[A] c) = _
  simp [Algebra.TensorProduct.map_tmul]

namespace dualizingModule

attribute [local instance] algebraDualModule

/-- An element of a scalar extension `S ⊗[A] C` killed by a map `C → B` that becomes bijective
after inverting `g` is killed by a power of `1 ⊗ g`. -/
private theorem baseChange_kernel_pow_torsion
    {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    (f : C →ₐ[A] B) (g : C)
    (hg : Function.Bijective (Localization.awayMap f.toRingHom g))
    (S : Type x) [CommRing S] [Algebra A S]
    (z : S ⊗[A] C)
    (hz : Algebra.TensorProduct.map (AlgHom.id S S) f z = 0) :
    ∃ n : ℕ, ((1 : S) ⊗ₜ[A] g : S ⊗[A] C) ^ n * z = 0 := by
  let Cg := Localization.Away g
  let Bg := Localization.Away (f g)
  have hmap (c : C) : Localization.awayMap f.toRingHom g (algebraMap C Cg c) =
      algebraMap B Bg (f c) := by
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  let f' : Cg →ₐ[A] Bg := {
    toRingHom := Localization.awayMap f.toRingHom g
    commutes' := by
      intro a
      change Localization.awayMap f.toRingHom g (algebraMap A Cg a) = _
      rw [IsScalarTower.algebraMap_apply A C Cg, hmap, f.commutes,
        ← IsScalarTower.algebraMap_apply A B Bg] }
  let e := AlgEquiv.ofBijective f' hg
  let eS : S ⊗[A] Cg ≃ₐ[S] S ⊗[A] Bg :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e
  let lC : S ⊗[A] C →ₐ[S] S ⊗[A] Cg :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom A C Cg)
  let lB : S ⊗[A] B →ₐ[S] S ⊗[A] Bg :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom A B Bg)
  have hcomm : eS.toAlgHom.comp lC =
      lB.comp (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
    ext c
    change (1 : S) ⊗ₜ[A] f' (algebraMap C Cg c) = (1 : S) ⊗ₜ[A] algebraMap B Bg (f c)
    rw [show f' (algebraMap C Cg c) = algebraMap B Bg (f c) from hmap c]
  have hlC : lC z = 0 := by
    apply eS.injective
    rw [map_zero]
    change (eS.toAlgHom.comp lC) z = 0
    rw [hcomm]
    change lB (Algebra.TensorProduct.map (AlgHom.id S S) f z) = 0
    rw [hz, map_zero]
  let eL := IsLocalization.Away.tensorProductEquivTMulRight A S g Cg
  have hloc : eL.toAlgHom.comp lC =
      IsScalarTower.toAlgHom S (S ⊗[A] C) (Localization.Away ((1 : S) ⊗ₜ[A] g)) := by
    ext c
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := A) (S := S) C g Cg 1 c
  have hzero : algebraMap (S ⊗[A] C) (Localization.Away ((1 : S) ⊗ₜ[A] g)) z = 0 := by
    change (IsScalarTower.toAlgHom S (S ⊗[A] C) _ ) z = 0
    rw [← hloc]
    change eL (lC z) = 0
    rw [hlC, map_zero]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq ((1 : S) ⊗ₜ[A] g)
    (hzero.trans (map_zero _).symm)
  exact ⟨n, by simpa using hn⟩

/-- The local annihilation hypothesis of `comparison_restrict_of_local_annihilation` holds for
the scalar extensions of a refinement of finite-open factorizations. -/
private theorem baseChange_refinement_local_annihilation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B))
    (S : Type y) [CommRing S] [Algebra A S] [IsNoetherianRing S]
    (p : PrimeSpectrum (S ⊗[A] B)) :
    ∃ c : (FiniteOpenFactorization.baseChange F S).middle,
      algebraMap (FiniteOpenFactorization.baseChange F S).middle (S ⊗[A] B) c
        ∉ p.asIdeal ∧
      ∃ n : ℕ, ∀ k : (FiniteOpenFactorization.baseChange H S).middle,
        algebraMap (FiniteOpenFactorization.baseChange H S).middle (S ⊗[A] B) k = 0 →
        (show (FiniteOpenFactorization.baseChange H S).middle from
          Algebra.TensorProduct.map (AlgHom.id S S) r c) ^ n * k = 0 := by
  let F₁ := FiniteOpenFactorization.baseChange F S
  let H₁ := FiniteOpenFactorization.baseChange H S
  let pB := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom p
  let pF := PrimeSpectrum.comap (algebraMap F.middle B) pB
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show pF ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨pB, rfl⟩)
      F.isOpenEmbedding_comap.isOpen_range
  refine ⟨1 ⊗ₜ[A] g, ?_, ?_⟩
  · rwa [finiteOpen_baseChange_algebraMap_tmul]
  · have hb := awayMap_bijective_refinement_at F r
      (RingHom.ext hr) hH g (F.awayMap_bijective g hg)
    let I : Ideal H₁.middle := RingHom.ker (algebraMap H₁.middle (S ⊗[A] B))
    have : IsNoetherianRing H₁.middle :=
      isNoetherian_of_tower S (inferInstance : IsNoetherian S H₁.middle)
    obtain ⟨n, hn⟩ := Submodule.exists_uniform_pow_annihilator I (IsNoetherian.noetherian I)
      (1 ⊗ₜ[A] r g) fun k hk => baseChange_kernel_pow_torsion
        (IsScalarTower.toAlgHom A H.middle B) (r g) hb S k hk
    exact ⟨n, fun k hk => hn k hk⟩

/-- Base change commutes with the canonical comparison along a refinement of finite-open
factorizations. -/
private theorem baseChange_refinement
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B))
    (S : Type y) [CommRing S] [Algebra A S] [IsNoetherianRing S]
    (ω : dualizingModule H) :
    dualizingModuleEquiv
        (FiniteOpenFactorization.baseChange H S)
        (FiniteOpenFactorization.baseChange F S)
        (dualizingModule.baseChange H S ω) =
      dualizingModule.baseChange F S (dualizingModuleEquiv H F ω) := by
  let F₁ := FiniteOpenFactorization.baseChange F S
  let H₁ := FiniteOpenFactorization.baseChange H S
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) :=
    Module.compHom _ (algebraMap B (S ⊗[A] B))
  let : Module B (dualizingModule H₁) :=
    Module.compHom _ (algebraMap B (S ⊗[A] B))
  let r₁ : F₁.middle →ₐ[S] H₁.middle :=
    Algebra.TensorProduct.map (AlgHom.id S S) r
  have hr₁ (c : F₁.middle) : algebraMap H₁.middle (S ⊗[A] B) (r₁ c) =
      algebraMap F₁.middle (S ⊗[A] B) c := by
    have hcomp : (IsScalarTower.toAlgHom A H.middle B).comp r =
        IsScalarTower.toAlgHom A F.middle B := AlgHom.ext hr
    have hh := DFunLike.congr_fun
      (Algebra.TensorProduct.map_comp (AlgHom.id S S) (AlgHom.id S S)
        (IsScalarTower.toAlgHom A H.middle B) r) c
    rw [hcomp] at hh
    exact hh.symm
  induction ω using TensorProduct.inductionOn with
  | add ω η hω hη =>
    change dualizingModule H at ω η
    change dualizingModuleEquiv H₁ F₁
      (dualizingModule.baseChange H S (ω + η)) =
      dualizingModule.baseChange F S (dualizingModuleEquiv H F (ω + η))
    simp only [map_add]
    exact congrArg₂ (· + ·) hω hη
  | tmul φ b =>
    change dualizingModuleEquiv H₁ F₁
      (dualizingModule.baseChange H S (dualizingModule.tmul H φ b)) =
      dualizingModule.baseChange F S
        (dualizingModuleEquiv H F (dualizingModule.tmul H φ b))
    have heq : dualizingModuleEquiv H F (dualizingModule.tmul H φ b) =
        dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
      simpa using dualizingModuleEquiv_tmul H F H hH (AlgHom.id A H.middle) r
        (fun _ => rfl) hr φ b
    rw [heq, dualizingModule.baseChange_tmul,
      dualizingModule.baseChange_tmul]
    have hdual : (φ.baseChange S).comp r₁.toLinearMap =
        Module.Dual.baseChange S (φ.comp r.toLinearMap) := by
      change (φ.baseChange S).comp
          (Algebra.TensorProduct.map (AlgHom.id S S) r).toLinearMap = _
      ext s
      simp [Module.Dual.baseChange_apply_tmul]
    rw [← hdual]
    exact comparison_restrict_of_local_annihilation F₁ H₁ r₁ hr₁
      (baseChange_refinement_local_annihilation F H r hr hH S) (φ.baseChange S) (1 ⊗ₜ[A] b)

/-- The base change map respects the canonical identification between dualizing
modules computed using two finite-open factorizations. -/
@[stacks 0BVC "independence of factorization"]
theorem baseChange_congr
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (A₁ : Type y) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁]
    (ω : dualizingModule F) :
    dualizingModuleEquiv
        (FiniteOpenFactorization.baseChange F A₁)
        (FiniteOpenFactorization.baseChange G A₁)
        (dualizingModule.baseChange F A₁ ω) =
      dualizingModule.baseChange G A₁
        (dualizingModuleEquiv F G ω) := by
  obtain ⟨H, rF, rG, hH, hF, hG⟩ := exists_common_finite_open_factorization F G
  obtain ⟨η, rfl⟩ := (dualizingModuleEquiv H F).surjective ω
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G₁ := FiniteOpenFactorization.baseChange G A₁
  let H₁ := FiniteOpenFactorization.baseChange H A₁
  have htrans : dualizingModuleEquiv F G
      (dualizingModuleEquiv H F η) = dualizingModuleEquiv H G η :=
    DFunLike.congr_fun (dualizingModuleEquiv_trans H F G) η
  have htrans₁ (η₁ : dualizingModule H₁) :
      dualizingModuleEquiv F₁ G₁
        (dualizingModuleEquiv H₁ F₁ η₁) =
          dualizingModuleEquiv H₁ G₁ η₁ :=
    DFunLike.congr_fun (dualizingModuleEquiv_trans H₁ F₁ G₁) η₁
  calc
    dualizingModuleEquiv F₁ G₁
        (dualizingModule.baseChange F A₁ (dualizingModuleEquiv H F η)) =
      dualizingModuleEquiv F₁ G₁
        (dualizingModuleEquiv H₁ F₁ (dualizingModule.baseChange H A₁ η)) :=
      congrArg (dualizingModuleEquiv F₁ G₁)
        (baseChange_refinement F H rF hF hH A₁ η).symm
    _ = dualizingModuleEquiv H₁ G₁
        (dualizingModule.baseChange H A₁ η) := htrans₁ _
    _ = dualizingModule.baseChange G A₁ (dualizingModuleEquiv H G η) :=
      baseChange_refinement G H rG hG hH A₁ η
    _ = dualizingModule.baseChange G A₁
        (dualizingModuleEquiv F G (dualizingModuleEquiv H F η)) :=
      congrArg (dualizingModule.baseChange G A₁) htrans.symm

end dualizingModule

end Stacks.Discriminant
