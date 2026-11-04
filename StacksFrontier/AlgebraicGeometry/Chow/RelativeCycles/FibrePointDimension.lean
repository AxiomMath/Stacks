module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField

/-!
# The relative dimension of a point of a scheme-theoretic fibre

Let `p : X ⟶ S` be locally of finite type, let `δ` be a dimension function on `S` and let `z` be
a point of the scheme-theoretic fibre `X_s`. The relative dimension of the image of `z` in `X`,
measured against `δ`, is the value `δ s` of the dimension function at the base point plus the
dimension of `z` computed inside the fibre, the latter being the relative dimension of `z` for
the Chow situation on `Spec κ(s)`, whose dimension function vanishes.

Both sides are `δ` of a base point plus a transcendence degree, so the statement amounts to two
comparisons: the image of `z` lies over `s`, and the residue field extension `κ(s) ⊆ κ(z)` read
in `X` agrees with the one read in the fibre over `Spec κ(s)`. The second is the composite of the
comparison of `κ(z)` with the residue field of its image in `X`, both taken over `κ(s)`, and of
the fact that `Spec κ(s) ⟶ S` is a preimmersion, so that its residue field map at the image of
`z` is an isomorphism and contributes nothing to the transcendence degree.

## Main results

* `Stacks.Chow.relativeDimension_fiberι` — the relative dimension over `S` of the image in `X`
  of a point of the fibre over `s` is `δ s` plus the dimension of that point in the fibre.

## Implementation notes

The two transcendence degrees are compared as cardinals, before `Cardinal.toNat` is applied, so
that the tower formula `trdeg_add_eq` can be used directly and no finiteness hypothesis is
needed to split a `Cardinal.toNat` over a sum. The tower is
`κ(s) → κ(q) → κ(z)`, where `q` is the image of `z` in `Spec κ(s)`; its scalar tower instance
comes from the factorisation `AlgebraicGeometry.Scheme.Hom.fiber_fac` of `X_s ⟶ X ⟶ S` through
`Spec κ(s)`, transported along the identification of the two base points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A point of a scheme-theoretic fibre lies over the base point of that fibre. -/
private theorem base_fiberι_aux {X S : Scheme.{u}} (p : X ⟶ S) (s : S) (z : p.fiber s) :
    p.base ((p.fiberι s).base z) = s := by
  have hx : (p.fiberι s).base z ∈ Set.range (p.fiberι s).base := ⟨z, rfl⟩
  rw [Scheme.Hom.range_fiberι] at hx
  exact hx

/-- An isomorphism of commutative rings is surjective on elements. -/
private theorem surjective_hom_of_isIso {A B : CommRingCat.{u}} (f : A ⟶ B) [IsIso f] :
    Function.Surjective f.hom := fun b =>
  ⟨(inv f).hom b, congrArg (fun g : B ⟶ B => g.hom b) (IsIso.inv_hom_id f)⟩

/-- The relative dimension over `S` of the image in `X` of a point `z` of the scheme-theoretic
fibre of `p` over `s` is the value `δ s` of the dimension function at `s` plus the dimension of
`z` inside the fibre. -/
theorem relativeDimension_fiberι {X S : Scheme.{u}}
    (δ : TopologicalSpace.DimensionFunction S) (p : X ⟶ S) [LocallyOfFiniteType p] (s : S)
    (z : p.fiber s) :
    relativeDimension δ p ((p.fiberι s).base z) = δ s + fiberPointDimension p s z := by
  have hs : p.base ((p.fiberι s).base z) = s := base_fiberι_aux p s z
  have hq : (S.fromSpecResidueField s).base ((p.fiberToSpecResidueField s).base z) = s := by
    have hmem : (S.fromSpecResidueField s).base ((p.fiberToSpecResidueField s).base z) ∈
      Set.range (S.fromSpecResidueField s).base := Set.mem_range_self _
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem
  have hbase : p.base ((p.fiberι s).base z) =
      (S.fromSpecResidueField s).base ((p.fiberToSpecResidueField s).base z) := hs.trans hq.symm
  let _ : Algebra (S.residueField (p.base ((p.fiberι s).base z)))
      (X.residueField ((p.fiberι s).base z)) :=
    (p.residueFieldMap ((p.fiberι s).base z)).hom.toAlgebra
  let _ : Algebra (S.residueField (p.base ((p.fiberι s).base z)))
      ((p.fiber s).residueField z) :=
    ((p.fiberι s ≫ p).residueFieldMap z).hom.toAlgebra
  let _ : Algebra ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z))
      ((p.fiber s).residueField z) :=
    ((p.fiberToSpecResidueField s).residueFieldMap z).hom.toAlgebra
  let _ : Algebra (S.residueField (p.base ((p.fiberι s).base z)))
      ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z)) :=
    ((S.residueFieldCongr hbase).hom ≫ (S.fromSpecResidueField s).residueFieldMap
      ((p.fiberToSpecResidueField s).base z)).hom.toAlgebra
  have htower : (p.fiberι s ≫ p).residueFieldMap z =
      (S.residueFieldCongr hbase).hom ≫ (S.fromSpecResidueField s).residueFieldMap
        ((p.fiberToSpecResidueField s).base z) ≫
          (p.fiberToSpecResidueField s).residueFieldMap z := by
    rw [Scheme.Hom.residueFieldMap_congr (p.fiber_fac s) z, Scheme.residueFieldMap_comp]
    rfl
  let _ : IsScalarTower (S.residueField (p.base ((p.fiberι s).base z)))
      ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z))
      ((p.fiber s).residueField z) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (fun m : CommRingCat.Hom _ _ => m.hom a) htower
  have : IsIso ((S.fromSpecResidueField s).residueFieldMap
      ((p.fiberToSpecResidueField s).base z)) :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  have hzero : Algebra.trdeg (S.residueField (p.base ((p.fiberι s).base z)))
      ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z)) = 0 :=
    trdeg_zero_of_surjective_algebraMap _ _
      (surjective_hom_of_isIso ((S.residueFieldCongr hbase).hom ≫
        (S.fromSpecResidueField s).residueFieldMap ((p.fiberToSpecResidueField s).base z)))
  have step1 : Algebra.trdeg (S.residueField (p.base ((p.fiberι s).base z)))
        ((p.fiber s).residueField z) =
      Algebra.trdeg (S.residueField (p.base ((p.fiberι s).base z)))
        (X.residueField ((p.fiberι s).base z)) :=
    AlgebraicGeometry.trdeg_residueField_fiber p s z
  have key : Algebra.trdeg (S.residueField (p.base ((p.fiberι s).base z)))
        (X.residueField ((p.fiberι s).base z)) =
      Algebra.trdeg
        ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z))
        ((p.fiber s).residueField z) := by
    rw [← step1, ← trdeg_add_eq (S.residueField (p.base ((p.fiberι s).base z)))
      ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z))
      (A := (p.fiber s).residueField z), hzero, zero_add]
  show δ (p.base ((p.fiberι s).base z)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p.base ((p.fiberι s).base z)))
        (X.residueField ((p.fiberι s).base z))) : ℤ) =
    δ s + (0 + (Cardinal.toNat (Algebra.trdeg
      ((Spec (S.residueField s)).residueField ((p.fiberToSpecResidueField s).base z))
      ((p.fiber s).residueField z)) : ℤ))
  rw [key, hs, zero_add]

end Stacks.Chow

end
