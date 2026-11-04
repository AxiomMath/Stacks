module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitExtSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology

/-!
# Vanishing of étale cohomology on a limit of affine base changes

Let `T` be an affine scheme, `X` an affine scheme over `T`, `(Z_i)` a directed system of affine
schemes over `T`, `Y_i = Z_i ×_T X` with limit `Y`, `p : Y ⟶ X` the projection and `F` an abelian
sheaf on `X_étale`. If `H^n(Y_i, π_i⁻¹ F) = 0` for every `i`, then `H^n(Y, p⁻¹ F) = 0`. This is
the vanishing form of [Stacks, Tag 03Q6] for an affine `X`, which is the case the proof of
[Stacks, Tag 0F0X] uses.

It is read off from [Stacks, Tag 09YQ] in the form
`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_of_qcqs`: every class of
`H^n(Y, f_{i₀}⁻¹ G)` comes from some level, for `G = π_{i₀}⁻¹ F` on a fixed level `Y_{i₀}`.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_limit_of_levels_of_isAffine`: the statement above.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology Stacks.EtaleCohomology.BaseChangeAlgebraSystem

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Vanishing on the levels of a system of affine base changes descends to the limit.** Let `I`
be a nonempty directed preorder, `T` an affine scheme, `X` an affine scheme over `T`,
`Z : Iᵒᵖ ⥤ Over T` a system of affine schemes over `T`, and `cY` a limit cone of the system
`Y_i = Z_i ×_T X` with a map `p : Y ⟶ X` through every projection `π_i : Y_i ⟶ X`. For an
abelian sheaf `F` on `X_ét` and a degree `n`, if `H^n(Y_i, π_i⁻¹ F) = 0` for all `i`, then
`H^n(Y, p⁻¹ F) = 0`: a class on the limit comes from some level (Stacks 09YQ,
`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_of_qcqs`), where it vanishes. -/
theorem subsingleton_sheafH_limit_of_levels_of_isAffine {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (T : Scheme.{u}) [IsAffine T] (X : Over T) [IsAffine X.left]
    (Z : Iᵒᵖ ⥤ Over T) [∀ i, IsAffine (Z.obj i).left]
    (F : Sheaf X.left.smallEtaleTopology Ab.{u + 1})
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (p : cY.pt ⟶ X.left) (hp : ∀ i, p = cY.π.app i ≫ pullback.snd (Z.obj i).hom X.hom) (n : ℕ)
    (h : ∀ i, Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAb (pullback.snd (Z.obj i).hom X.hom)).obj F) n)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb p).obj F) n) := by
  let D := baseChange T X Z
  let π : ∀ i, D.obj i ⟶ X.left := fun i => pullback.snd (Z.obj i).hom X.hom
  have hπ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), π i = D.map a ≫ π j := fun a =>
    (Over.w ((Z ⋙ Over.pullback X.hom).map a)).symm
  let i₀ : I := Classical.arbitrary I
  let G := (etaleAbelianInverseImage.{u, 0} (π (op i₀))).obj F
  -- the levels, read with the inverse image of `G`
  have hlev : ∀ (i : I) (hi : i₀ ≤ i), Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE hi).op)).obj G) n) := fun i hi =>
    (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
      ((LimitExt.K (D.map (homOfLE hi).op) (π (op i₀)) (π (op i)) (hπ _)).app F) n).1 <|
      (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (π (op i))).app F) n).1 (h (op i))
  -- the limit
  refine (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage p).app F) n).2 ?_
  refine (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
    ((LimitExt.K (cY.π.app (op i₀)) (π (op i₀)) p (hp _)).app F) n).2 ?_
  suffices hz : ∀ z : Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (cY.π.app (op i₀))).obj G) n, z = 0 from
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro z
  obtain ⟨i, hi, y, hy⟩ := LimitExt.exists_le_restriction_eq_of_qcqs D cY hcY i₀ G n z
  rw [← hy, (hlev i hi).elim y 0, map_zero, Ext.zero_comp]

end AlgebraicGeometry

end
