module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree

/-!
# The number of `k`-points killed by an étale multiplication

Let `k` be an algebraically closed field, `A` an abelian variety over `k` and `d` an integer
invertible in `k`.  Multiplication by `d` is then étale
(`Stacks.Groupoids.etale_zpow_id_of_isAlgClosed_of_isUnit`), and if it is finite locally free of
rank `r`, then exactly `r` of the `k`-points of `A` are carried to the unit by `[d]`.

## Main results

* `Stacks.Groupoids.kernelPointsEquivSections`: the `k`-points of `A` killed by `[d]` are the
  sections of the fibre of `[d]` over the unit point.
* `Stacks.Groupoids.natCard_kernelPoints_eq_of_isFiniteLocallyFreeOfRank`: if `[d]` is finite
  locally free of rank `r` and `d` is invertible in `k`, then
  `#{p ∈ A(k) | d • p = 0} = r`.
* `Stacks.Groupoids.natCard_kernelPoints_of_hasTheoremOfTheCube`: from the theorem of the cube
  for `A`, the number of `k`-points killed by a natural number `d ≥ 1` invertible in `k` is
  `d ^ (2 dim A)`.

## Implementation notes

The fibre of `[d]` over the unit point is a scheme over `Spec k` which is finite, étale and
finite locally free of rank `r`, being a base change of `[d]`.  A finite étale scheme over a
separably closed field is finite locally free of rank the number of its rational points
(`Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections`), and the rank of a finite locally
free morphism to a nonempty scheme is unique.  The `k`-points of the fibre are the `k`-points of
`A` which `[d]` carries to the unit, by the universal property of the fibre product; a morphism
`Spec k ⟶ A` with this property is automatically a morphism over `k`, because `[d]` and the unit
are.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The `k`-points of a group scheme `A` killed by multiplication by `d` are the sections of the
fibre of `[d]` over the unit point. -/
noncomputable def kernelPointsEquivSections (d : ℤ) :
    {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ d = η[A]} ≃
      {σ : Spec (.of k) ⟶ pullback ((𝟙 A : A ⟶ A) ^ d).left (η[A]).left //
        σ ≫ pullback.snd ((𝟙 A : A ⟶ A) ^ d).left (η[A]).left = 𝟙 _} where
  toFun p := ⟨pullback.lift p.1.left (𝟙 _) (by
      rw [Category.id_comp, ← Over.comp_left, p.2]), pullback.lift_snd _ _ _⟩
  invFun σ := ⟨Over.homMk (σ.1 ≫ pullback.fst _ _) (by
      have h1 : ((𝟙 A : A ⟶ A) ^ d).left ≫ A.hom = A.hom := Over.w _
      have h2 : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w (η[A])
      change (σ.1 ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _
      rw [← h1, Category.assoc, reassoc_of% (pullback.condition (f := ((𝟙 A : A ⟶ A) ^ d).left)
        (g := (η[A]).left)), h2, Category.comp_id, σ.2]), by
      ext1
      change (σ.1 ≫ pullback.fst _ _) ≫ ((𝟙 A : A ⟶ A) ^ d).left = (η[A]).left
      rw [Category.assoc, pullback.condition, reassoc_of% σ.2]⟩
  left_inv p := Subtype.ext (Over.OverMorphism.ext (pullback.lift_fst _ _ _))
  right_inv σ := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans σ.2.symm))

/-- **The number of `k`-points killed by an étale multiplication is its rank.** Let `k` be
algebraically closed, `A` an abelian variety over `k` and `d` an integer invertible in `k`.  If
multiplication by `d` is finite locally free of rank `r`, then exactly `r` of the `k`-points of
`A` are carried to the unit by multiplication by `d`. -/
theorem natCard_kernelPoints_eq_of_isFiniteLocallyFreeOfRank [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) (hd : IsUnit ((d : ℤ) : k)) (r : ℕ)
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left r) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ d = η[A]} = r := by
  have := etale_zpow_id_of_isAlgClosed_of_isUnit k A d hd
  have : IsFinite ((𝟙 A : A ⟶ A) ^ d).left :=
    (isFinite_zpow_id_left_iff_isAffineHom A d).mpr hr.toIsAffineHom
  let g := pullback.snd ((𝟙 A : A ⟶ A) ^ d).left (η[A]).left
  have sq : IsPullback (pullback.fst _ _) g ((𝟙 A : A ⟶ A) ^ d).left (η[A]).left :=
    .of_hasPullback _ _
  have : IsFinite g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsFinite) sq inferInstance
  have : Etale g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale) sq inferInstance
  have : Flat g := inferInstance
  have hg : Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r :=
    have := hr
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback sq
  have hN := Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections (Ω := k) g
  rw [Nat.card_congr (kernelPointsEquivSections A d)]
  have h1 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g _).mp hN
    (IsLocalRing.closedPoint k)
  have h2 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g r).mp hg
    (IsLocalRing.closedPoint k)
  exact h1.symm.trans h2

/-- From the theorem of the cube for `A × A × A`, the number of `k`-points of an abelian variety
over an algebraically closed field killed by a natural number `d ≥ 1` invertible in `k` is
`d ^ (2 dim A)`: multiplication by `d` is finite locally free of that rank
(`isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube`). -/
theorem natCard_kernelPoints_of_hasTheoremOfTheCube [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (hcube : HasTheoremOfTheCube A) (d : ℕ)
    (hd0 : d ≠ 0) (hd : IsUnit (d : k)) :
    Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]} =
      d ^ (2 * abelianVarietyDimension A) := by
  have h := isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A hcube (d : ℤ)
    (by exact_mod_cast hd0)
  rw [Int.natAbs_natCast] at h
  exact natCard_kernelPoints_eq_of_isFiniteLocallyFreeOfRank A (d : ℤ) (by simpa using hd) _ h

end Stacks.Groupoids

end
