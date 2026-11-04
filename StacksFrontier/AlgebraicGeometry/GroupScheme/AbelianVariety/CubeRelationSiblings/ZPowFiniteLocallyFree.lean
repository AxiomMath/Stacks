module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelationSiblings.ZPowPullback

/-!
# Multiplication by `d` on an abelian variety is finite locally free, from the cube relation

The chain of `StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/ZPowFiniteLocallyFree.lean`
— `[d]` is finite, flat, finite locally free, of degree `|d| ^ (2 dim A)` and finite locally free
of that rank, for `d ≠ 0` — takes `HasTheoremOfTheCube A` and uses it only through the closed form
of the class of `[n]^*L` (`Stacks.Groupoids.zpowIdPicardClass_eq`, at the symmetric ample module).
This file is that chain under `Stacks.Groupoids.HasCubeRelation A`
(`CubeRelationSiblings/ZPowPullback.lean`), through
`Stacks.Groupoids.zpowIdPicardClass_eq_of_hasCubeRelation`; the proofs are those of the original
chain, with that one input replaced, and reuse its hypothesis-free lemmas.

## Main results

* `Stacks.Groupoids.isFinite_zpow_id_left_of_hasCubeRelation`,
  `Stacks.Groupoids.flat_zpow_id_left_of_hasCubeRelation`,
  `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_of_hasCubeRelation`,
  `Stacks.Groupoids.degreeOver_zpow_id_left_of_hasCubeRelation`.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_hasCubeRelation`: `[d]` is finite
  locally free of rank `|d| ^ (2 dim A)` for `d ≠ 0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Groupoids

open scoped CategoryTheory.MonObj
open Stacks.SheafOfModules (schemeTensor schemeTensorPower picardClass pullbackPicardClass
  isInvertible_schemeTensor pullbackPicardClass_comp pullbackPicardClass_id
  pullbackPicardClass_schemeTensor picardClass_schemeTensor)

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Tag 0BFF for a symmetric module, from the cube relation.** If `[-1]^* N ≅ N`, then
`[n]^* N ≅ N^{⊗ n²}` for every integer `n`, given `HasCubeRelation A`. The sibling of
`Stacks.Groupoids.nonempty_zpowId_pullback_iso_of_symmetric`. -/
theorem nonempty_zpowId_pullback_iso_of_symmetric_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcr : HasCubeRelation A)
    (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (e : pullbackOver (ι : A ⟶ A) N ≅ N) (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) N ≅ schemeTensorPower A.left N hN (n * n)) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver ((𝟙 A : A ⟶ A) ^ n) N hN)
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left N hN (n * n))).mp ?_
  have hι : pullbackPicardClass (ι : A ⟶ A).left N hN =
      picardClass A.left.presheaf A.left.ringCatIsSheaf N hN :=
    (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _ _ hN).mpr
      ⟨e⟩
  have key := zpowIdPicardClass_eq_of_hasCubeRelation A N hN hcr n
  rw [hι, ← add_smul, triangularNumber_add_triangularNumber_neg] at key
  exact key.trans (Stacks.SheafOfModules.picardClass_schemeTensorPower A.left N hN (n * n)).symm

/-- **Multiplication by a nonzero integer on an abelian variety is finite**, given the cube
relation for `A`. For the symmetric ample module `N`, `[d]^* N ≅ N^{⊗ d²}` is ample, and a
proper morphism along which an invertible module pulls back to an ample one is finite. -/
theorem isFinite_zpow_id_left_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcr : HasCubeRelation A) (d : ℤ) (hd : d ≠ 0) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left := by
  obtain ⟨N, hN, hNa, ⟨e⟩⟩ := exists_isAmple_symmetric A
  obtain ⟨f⟩ := nonempty_zpowId_pullback_iso_of_symmetric_of_hasCubeRelation A hcr N hN e d
  have := isProper_zpow_id_left A d
  have hm : 1 ≤ d.natAbs * d.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hd)
      (Int.natAbs_ne_zero.mpr hd))
  have hpow := Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple N _ hm hNa
  have hcast : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := Int.natAbs_mul_self
  rw [hcast] at hpow
  have hinv : Stacks.Ample.IsInvertibleModule A.left (pullbackOver ((𝟙 A : A ⟶ A) ^ d) N) :=
    modulePullback_isInvertible_scheme _ N
  have hample : Stacks.Ample.IsAmple A.left (pullbackOver ((𝟙 A : A ⟶ A) ^ d) N) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (f ≪≫ Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso A.left N (d * d))).mpr hpow
  exact isFinite_of_isProper_of_isAmple_modulePullback _ (isAffineHom_fromSpecResidueField A) N
    hample

/-- A finite multiplication-by-`d` morphism on an abelian variety is surjective. -/
private theorem surjective_zpow_id_left_of_isFinite
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    [IsFinite ((𝟙 A : A ⟶ A) ^ d).left] : Surjective ((𝟙 A : A ⟶ A) ^ d).left :=
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have := isLocallyNoetherian_left A
  have : IsNoetherian A.left := {}
  surjective_of_isFinite_of_topologicalKrullDim_le _
    (topologicalKrullDim_ne_top_of_isProper k A.hom) le_rfl

/-- **Multiplication by a nonzero integer on an abelian variety is flat**, given the cube
relation for `A`. It is finite (`isFinite_zpow_id_left_of_hasCubeRelation`), hence surjective,
the source and target being the same irreducible variety; so it preserves the dimension of every
local ring, the target being universally catenary, and the local rings of the smooth variety `A`
are regular. By miracle flatness ([Stacks, Tag 00R4]) every stalk map is flat. -/
theorem flat_zpow_id_left_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcr : HasCubeRelation A) (d : ℤ) (hd : d ≠ 0) :
    Flat ((𝟙 A : A ⟶ A) ^ d).left := by
  have := isFinite_zpow_id_left_of_hasCubeRelation A hcr d hd
  have := smooth_hom A
  have := isLocallyNoetherian_left A
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := {}
  have hsurj := surjective_zpow_id_left_of_isFinite A d
  have hdom : IsDominant ((𝟙 A : A ⟶ A) ^ d).left := inferInstance
  have hS := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k A.hom
  rw [Flat.iff_flat_stalkMap]
  intro x
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom x
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom (((𝟙 A : A ⟶ A) ^ d).left x)
  exact flat_stalkMap_of_quasiFiniteAt _ x (Scheme.Hom.quasiFiniteAt _ x)
    (ringKrullDim_stalk_eq_of_locallyQuasiFinite _ hS x)

/-- **Multiplication by a nonzero integer on an abelian variety is finite locally free**, given
the cube relation for `A`: it is finite and flat, over a locally Noetherian base. -/
theorem isFiniteLocallyFree_zpow_id_left_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcr : HasCubeRelation A) (d : ℤ) (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left :=
  have := isFinite_zpow_id_left_of_hasCubeRelation A hcr d hd
  have := flat_zpow_id_left_of_hasCubeRelation A hcr d hd
  isFiniteLocallyFree_of_isFinite_of_flat A _

/-- **The degree of multiplication by a nonzero integer `d` on an abelian variety is
`|d| ^ (2 dim A)`**, given the cube relation for `A`. For the symmetric ample module `N`,
`[d]^* N ≅ N^{⊗ d²}`, so by [Stacks, Tag 0BEX]
`deg([d]) (N^g · A) = ([d]^* N^g · A) = ((N^{⊗ d²})^g · A) = d^{2g} (N^g · A)`, and
`(N^g · A) > 0` ([Stacks, Tag 0BEV]). -/
theorem degreeOver_zpow_id_left_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcr : HasCubeRelation A) (d : ℤ) (hd : d ≠ 0) :
    haveI := isFinite_zpow_id_left_of_hasCubeRelation A hcr d hd
    haveI : Surjective ((𝟙 A : A ⟶ A) ^ d).left :=
      have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
      have := isLocallyNoetherian_left A
      have : IsNoetherian A.left := {}
      surjective_of_isFinite_of_topologicalKrullDim_le _
        (topologicalKrullDim_ne_top_of_isProper k A.hom) le_rfl
    degreeOver ((𝟙 A : A ⟶ A) ^ d).left = d.natAbs ^ (2 * abelianVarietyDimension A) := by
  have := isFinite_zpow_id_left_of_hasCubeRelation A hcr d hd
  have := surjective_zpow_id_left_of_isFinite A d
  set f := ((𝟙 A : A ⟶ A) ^ d).left with hfdef
  set g := abelianVarietyDimension A
  have hdim := topologicalKrullDim_eq_abelianVarietyDimension A
  obtain ⟨N, hN, hNa, ⟨e⟩⟩ := exists_isAmple_symmetric A
  obtain ⟨e₁⟩ := nonempty_zpowId_pullback_iso_of_symmetric_of_hasCubeRelation A hcr N hN e d
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2 N := hN
  have hfp : f ≫ A.hom = A.hom := zpow_id_left_comp_hom A d
  have : IsVariety k (f ≫ A.hom) := by rw [hfp]; infer_instance
  have : IsProper (f ≫ A.hom) := by rw [hfp]; infer_instance
  have h0BEX := selfIntersectionNumber_pullback_of_isFinite k A.hom f g hdim N
  have hcongr : ∀ {p p' : A.left ⟶ Spec (.of k)} (h : p = p') [IsProper p] [IsProper p']
      (M : A.left.Modules) [SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2 M],
      selfIntersectionNumber k p (𝟙 A.left) g hdim.le M =
        selfIntersectionNumber k p' (𝟙 A.left) g hdim.le M := by
    intro p p' h _ _ M _
    subst h
    rfl
  rw [hcongr hfp] at h0BEX
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj N) := modulePullback_isInvertible_scheme f N
  set m := d.natAbs * d.natAbs with hm
  have hcast : ((m : ℕ) : ℤ) = d * d := Int.natAbs_mul_self
  have e₂ : (Scheme.Modules.pullback f).obj N ≅
      Stacks.SheafOfModules.Invertible.tensorPower A.left.presheaf A.left.ringCatSheaf.2 N
        ((m : ℕ) : ℤ) :=
    e₁ ≪≫ eqToIso (by rw [hcast]; rfl)
  rw [selfIntersectionNumber_eq_of_iso k A.hom (𝟙 A.left) g _ _ _ e₂,
    selfIntersectionNumber_tensorPower] at h0BEX
  have hpos := selfIntersectionNumber_pos k A.hom (𝟙 A.left) g hdim N
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple A.left N hNa)
  have key : (degreeOver f : ℤ) = (m : ℤ) ^ g :=
    (mul_right_cancel₀ hpos.ne' h0BEX).symm
  have : degreeOver f = m ^ g := by exact_mod_cast key
  rw [this, hm, ← pow_two, ← pow_mul]

/-- **Multiplication by a nonzero integer `d` on an abelian variety is finite locally free of
degree `|d| ^ (2 dim A)`**, given the cube relation for `A` (`HasCubeRelation A`). The sibling of
`Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube`.

The morphism is finite and flat (`isFiniteLocallyFree_zpow_id_left_of_hasCubeRelation`), its rank
is the degree of the extension of function fields (`isFiniteLocallyFreeOfRank_degreeOver`), and
that degree is `|d| ^ (2 dim A)` (`degreeOver_zpow_id_left_of_hasCubeRelation`). -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_hasCubeRelation
    [AlgebraicGeometry.IsAbelianVariety k A] (hcr : HasCubeRelation A) (d : ℤ)
    (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left
      (d.natAbs ^ (2 * abelianVarietyDimension A)) := by
  have := isFinite_zpow_id_left_of_hasCubeRelation A hcr d hd
  have := isFiniteLocallyFree_zpow_id_left_of_hasCubeRelation A hcr d hd
  have := surjective_zpow_id_left_of_isFinite A d
  have hgen := genericPoint_eq_of_surjective ((𝟙 A : A ⟶ A) ^ d).left
  have h := isFiniteLocallyFreeOfRank_degreeOver ((𝟙 A : A ⟶ A) ^ d).left hgen
    (preimage_genericPoint_of_locallyQuasiFinite _ hgen)
  rwa [degreeOver_zpow_id_left_of_hasCubeRelation A hcr d hd] at h

end Stacks.Groupoids

end
