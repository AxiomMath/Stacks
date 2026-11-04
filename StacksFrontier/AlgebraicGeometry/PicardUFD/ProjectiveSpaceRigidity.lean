module

public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rigidity of invertible modules on projective space over a unique factorization domain

Let `A` and `B` be unique factorization domains and let `r : Spec A ⟶ Spec B` be a morphism with a
section `p : Spec B ⟶ Spec A`, `p ≫ r = 𝟙`. Pulling back along the induced morphism of projective
spaces `ι_p : ℙᵐ_B ⟶ ℙᵐ_A` is then **injective** on Picard groups: an invertible module on `ℙᵐ_A`
which becomes trivial on the fibre `ℙᵐ_B` over `p` is already trivial on `ℙᵐ_A`, and so is trivial
on the fibre over every other point.

This is the rigidity half of the last paragraph of the proof of Stacks 0FH9 ("an invertible
module on `T × ℙᵐ` whose fibre over `p` is trivial has trivial fibre over `q`"), in the case of a
base `T = Spec A` with `A` a unique factorization domain, where it needs no Euler characteristic.

## The argument

By Stacks 0BXJ (`Stacks.PicardUFD.twistPicardAddEquiv`) both `Pic(ℙᵐ_A)` and `Pic(ℙᵐ_B)` are
isomorphic to `ℤ` for `0 < m`, and both vanish for `m = 0`. The induced morphism
`ρ : ℙᵐ_A ⟶ ℙᵐ_B` of `r` satisfies `ι_p ≫ ρ = 𝟙` by functoriality, so `ι_p^* ∘ ρ^* = id` and
`ι_p^*` is surjective. A surjective endomorphism of `ℤ` is multiplication by a unit, hence
injective.

Projective space here is the library's base-change model
`AlgebraicGeometry.projectiveSpaceOverRing`, which is functorial in the base on the nose
(`AlgebraicGeometry.projectiveSpaceOverMap`). Stacks 0BXJ is proved for the model
`Proj A[T₀, …, Tₘ]`, and is carried across by the comparison
`Stacks.ProjectiveCohomology.projModelIso`. No twisting sheaf is used: only the abstract
isomorphism with `ℤ`.

## Main definitions

* `Stacks.PicardUFD.projectiveSpaceOverRingPicardAddEquiv`: `ℤ ≃+ Pic(ℙᵐ_A)` for `A` a unique
  factorization domain and `0 < m`.

## Main results

* `Stacks.PicardUFD.subsingleton_picardGroup_projectiveSpaceOverRing_zero`: `Pic(ℙ⁰_A) = 0`.
* `Stacks.PicardUFD.injective_pullbackPicardHom_projectiveSpaceOverMap`: **pullback to the fibre
  over a section is injective on Picard groups.**
* `Stacks.PicardUFD.eq_zero_of_pullbackPicardHom_projectiveSpaceOverMap_eq_zero`: the same, as
  the vanishing of a class with vanishing restriction.

## References

* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.PicardUFD

open Stacks.SheafOfModules

attribute [local instance] MvPolynomial.gradedAlgebra

section Equiv

variable (A : Type u) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- **Stacks 0BXJ on the base-change model of projective space:** `ℤ ≃+ Pic(ℙᵐ_A)` for `A` a
unique factorization domain and `0 < m`, transported from `Proj A[T₀, …, Tₘ]` along
`Stacks.ProjectiveCohomology.projModelIso`. -/
def projectiveSpaceOverRingPicardAddEquiv (m : ℕ) (hm : 0 < m) :
    ℤ ≃+ (projectiveSpaceOverRing m (CommRingCat.of A)).picardGroup :=
  (twistPicardAddEquiv A m hm).trans
    (picardGroupAddEquivOfIso (Stacks.ProjectiveCohomology.projModelIso A m))

/-- **The Picard group of `ℙ⁰_A` is trivial** for `A` a unique factorization domain. -/
@[ega "I 2.4.8"]
theorem subsingleton_picardGroup_projectiveSpaceOverRing_zero :
    Subsingleton (projectiveSpaceOverRing 0 (CommRingCat.of A)).picardGroup := by
  have := subsingleton_picardGroup_dim_zero A
  exact (picardGroupAddEquivOfIso
    (Stacks.ProjectiveCohomology.projModelIso A 0)).symm.injective.subsingleton

end Equiv

/-- A surjective additive endomorphism of `ℤ` is injective. -/
@[sga "3 X 3.8" "Rank-one free case"]
theorem _root_.AddMonoidHom.injective_of_surjective_int (h : ℤ →+ ℤ)
    (hs : Function.Surjective h) : Function.Injective h := by
  have hmul : ∀ a : ℤ, h a = a * h 1 := fun a => by
    rw [← smul_eq_mul, ← map_zsmul, smul_eq_mul, mul_one]
  obtain ⟨n, hn⟩ := hs 1
  rw [hmul] at hn
  have hc : h 1 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hn; exact zero_ne_one hn
  refine (injective_iff_map_eq_zero h).mpr fun a ha => ?_
  rw [hmul] at ha
  exact (mul_eq_zero.mp ha).resolve_right hc

variable {A B : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]

/-- **Pullback to the fibre over a section is injective on Picard groups.** Let
`r : Spec A ⟶ Spec B` have a section `p`, with `A` and `B` unique factorization domains. Then the
pullback along the induced morphism `ℙᵐ_B ⟶ ℙᵐ_A` is injective on Picard groups. -/
theorem injective_pullbackPicardHom_projectiveSpaceOverMap (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (p : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _) :
    Function.Injective (pullbackPicardHom (projectiveSpaceOverMap m p)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := subsingleton_picardGroup_projectiveSpaceOverRing_zero A
    exact fun x y _ => Subsingleton.elim x y
  have hsec : (pullbackPicardHom (projectiveSpaceOverMap m p)).comp
      (pullbackPicardHom (projectiveSpaceOverMap m r)) = AddMonoidHom.id _ := by
    rw [← pullbackPicardHom_comp, projectiveSpaceOverMap_comp, hp, projectiveSpaceOverMap_id,
      pullbackPicardHom_id]
  let α := projectiveSpaceOverRingPicardAddEquiv A m hm
  let β := projectiveSpaceOverRingPicardAddEquiv B m hm
  have hf : Function.Surjective (pullbackPicardHom (projectiveSpaceOverMap m p)) := fun y =>
    ⟨_, DFunLike.congr_fun hsec y⟩
  let h : ℤ →+ ℤ := β.symm.toAddMonoidHom.comp
    ((pullbackPicardHom (projectiveSpaceOverMap m p)).comp α.toAddMonoidHom)
  have hinj : Function.Injective (pullbackPicardHom (projectiveSpaceOverMap m p) ∘ α) :=
    Function.Injective.of_comp (f := β.symm)
      (h.injective_of_surjective_int (β.symm.surjective.comp (hf.comp α.surjective)))
  exact fun x y hxy => α.symm.injective (hinj (by simpa using hxy))

/-- **An invertible module on `ℙᵐ_A` trivial on the fibre over a section is trivial.** Read on
Picard classes: a class whose pullback to `ℙᵐ_B` along the section vanishes is zero. -/
theorem eq_zero_of_pullbackPicardHom_projectiveSpaceOverMap_eq_zero (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (p : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (x : (projectiveSpaceOverRing m (CommRingCat.of A)).picardGroup)
    (hx : pullbackPicardHom (projectiveSpaceOverMap m p) x = 0) : x = 0 :=
  injective_pullbackPicardHom_projectiveSpaceOverMap m r p hp (hx.trans (map_zero _).symm)

end Stacks.PicardUFD

end
