module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree

/-!
# The generic point of a nonzero abelian variety has infinite order

Let `A` be an abelian variety over a field `k` and let `K = k(A)` be its function field. The
generic point of `A` is a `K`-valued point `η : Spec K → A` over `k`, that is, an element of the
group of morphisms `Spec K ⟶ A` in schemes over `Spec k`. If `A` is nonzero, this element has
infinite order.

The reason is that multiplication by a nonzero integer `n` is surjective (Stacks 03RP, part (3)),
so it maps the generic point of the irreducible scheme `A` to the generic point. If `η ^ n` were
the neutral element, the generic point would lie in the image of the unit section, which is a
closed point; then `A` would be a point, of dimension zero.

## Main results

* `Stacks.Groupoids.zpow_id_left_genericPoint`: for `n ≠ 0`, `[n]` fixes the generic point.
* `Stacks.Groupoids.genericPointHom`: the generic point, as a morphism over `Spec k` from the
  spectrum of the function field.
* `Stacks.Groupoids.not_isOfFinOrder_genericPointHom`: for `A` of positive dimension, the generic
  point has infinite order in the group of `k(A)`-valued points.

## Implementation notes

This is the non-torsion point used in the formalization of Stacks 0CXX, which glues along it
instead of along a non-torsion rational point of `A(k)`: the latter needs, for countable `k`, a
theorem of Frey and Jarden that is not in the library.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The underlying scheme of an abelian variety is irreducible. -/
instance irreducibleSpace_left_of_isAbelianVariety [AlgebraicGeometry.IsAbelianVariety k A] :
    IrreducibleSpace A.left :=
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  inferInstance

/-- Multiplication by a nonzero integer on an abelian variety fixes the generic point: it is
surjective, so every point is a specialization of the image of the generic point. -/
theorem zpow_id_left_genericPoint [AlgebraicGeometry.IsAbelianVariety k A] (n : ℤ)
    (hn : n ≠ 0) :
    ((𝟙 A : A ⟶ A) ^ n).left (genericPoint A.left) = genericPoint A.left := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hsurj := (surjective_zpow_id k A n hn).surj
  set f : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ n).left
  have hgen : IsGenericPoint (f (genericPoint A.left)) (⊤ : Set A.left) := by
    refine isGenericPoint_iff_specializes.mpr fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact (genericPoint_specializes x).map f.continuous
  exact hgen.eq (genericPoint_spec A.left)

/-- The generic point of a group scheme `A` over `Spec k`, as an object of schemes over `Spec k`:
the spectrum of the function field of `A`, mapped to `Spec k` through `A`. -/
noncomputable abbrev genericPointOver [IrreducibleSpace A.left] : Over (Spec (.of k)) :=
  Over.mk (A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom)

/-- The generic point of a group scheme `A` over `Spec k`, as a `k(A)`-valued point of `A`. -/
noncomputable abbrev genericPointHom [IrreducibleSpace A.left] : genericPointOver A ⟶ A :=
  Over.homMk (A.left.fromSpecStalk (genericPoint A.left))

/-- If the generic point of an irreducible scheme over a field lies in the image of a section of
its structure morphism, the scheme has dimension zero. -/
theorem topologicalKrullDim_le_zero_of_genericPoint_mem_range
    [AlgebraicGeometry.IsAbelianVariety k A]
    (h : genericPoint A.left ∈ Set.range (η[A]).left) :
    topologicalKrullDim A.left ≤ 0 := by
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  obtain ⟨s, hs⟩ := h
  have hsub : Subsingleton A.left := by
    have hcl : IsClosed ({(η[A]).left s} : Set A.left) := by
      have hrange : Set.range (η[A]).left = {(η[A]).left s} := by
        ext y
        refine ⟨?_, fun hy => ⟨s, hy.symm⟩⟩
        rintro ⟨t, rfl⟩
        rw [Subsingleton.elim t s]
        rfl
      rw [← hrange]
      exact (η[A]).left.isClosedEmbedding.isClosed_range
    refine ⟨fun x y => ?_⟩
    have hx := (genericPoint_specializes x).mem_closed hcl (by rw [← hs]; rfl)
    have hy := (genericPoint_specializes y).mem_closed hcl (by rw [← hs]; rfl)
    exact hx.trans hy.symm
  have : DiscreteTopology A.left := ⟨Subsingleton.elim _ _⟩
  exact topologicalKrullDim_zero_of_discreteTopology A.left

/-- **The generic point of a nonzero abelian variety has infinite order.** Let `A` be an abelian
variety of positive dimension over a field `k`. The generic point of `A`, a `k(A)`-valued point
of `A`, is not of finite order in the group of `k(A)`-valued points. -/
theorem not_isOfFinOrder_genericPointHom [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 1 ≤ abelianVarietyDimension A) : ¬ IsOfFinOrder (genericPointHom A) := by
  intro h
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcomp : genericPointHom A ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) =
      toUnit (genericPointOver A) ≫ η[A] := by
    rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast, hpow]
    rfl
  let pt : (genericPointOver A).left :=
    IsLocalRing.closedPoint (A.left.presheaf.stalk (genericPoint A.left))
  have hpt := congrArg (fun g : genericPointOver A ⟶ A => g.left pt) hcomp
  have e1 : (genericPointHom A ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ)).left pt = genericPoint A.left := by
    change ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left (A.left.fromSpecStalk (genericPoint A.left)
      (IsLocalRing.closedPoint (A.left.presheaf.stalk (genericPoint A.left)))) = _
    rw [Scheme.fromSpecStalk_closedPoint, zpow_id_left_genericPoint A _ hn0]
  have e2 : (η[A]).left ((toUnit (genericPointOver A)).left pt) = genericPoint A.left :=
    hpt.symm.trans e1
  have h0 := topologicalKrullDim_le_zero_of_genericPoint_mem_range A ⟨_, e2⟩
  have hle : (topologicalKrullDim A.left).unbotD 0 = 0 := by
    cases h : topologicalKrullDim A.left with
    | bot => rfl
    | coe x =>
      have hx : (x : WithBot ℕ∞) ≤ 0 := h ▸ h0
      simp only [WithBot.unbotD_coe]
      exact nonpos_iff_eq_zero.mp (by exact_mod_cast hx)
  simp [abelianVarietyDimension, hle] at hA

end Stacks.Groupoids

end
