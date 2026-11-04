module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Changing the target of a Hom complex along an isomorphism

Let `K`, `M` and `M'` be cochain complexes in a preadditive category and let `e : M ≅ M'`. The
Hom complexes `Hom^•(K, M)` and `Hom^•(K, M')` are isomorphic, degreewise by postcomposition of
a homogeneous cochain with `e`.

## Main definitions

* `CochainComplex.HomComplex.cochainTargetEquiv`: postcomposition with `e` on the homogeneous
  cochains of a fixed degree, as an isomorphism of additive groups.
* `CochainComplex.HomComplex.targetIso`: **the isomorphism of Hom complexes.**

## Main results

* `CochainComplex.HomComplex.targetIso_hom_apply_v`: the isomorphism postcomposes each local
  component of a cochain with the corresponding component of `e`.

## Implementation notes

Compatibility with the differential `CochainComplex.HomComplex.δ` is `δ_comp_ofHom`, which says
that the differential of a cochain postcomposed with a morphism of complexes is the
postcomposition of its differential: a degree-`0` cochain coming from a morphism of complexes is
a cocycle, so the Leibniz rule `δ_comp` has only one surviving term. Nothing here needs `e` to
be an isomorphism except the inverse, so the construction is an `AddEquiv` in each degree and
the isomorphism of complexes is assembled by `HomologicalComplex.Hom.isoOfComponents`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] (K : CochainComplex V ℤ)
  {M M' : CochainComplex V ℤ}

/-- Postcomposition with an isomorphism `e : M ≅ M'` of the target, on the homogeneous cochains
of degree `n` from `K`. -/
def cochainTargetEquiv (e : M ≅ M') (n : ℤ) : Cochain K M n ≃+ Cochain K M' n where
  toFun z := z.comp (Cochain.ofHom e.hom) (add_zero n)
  invFun z := z.comp (Cochain.ofHom e.inv) (add_zero n)
  left_inv z := by
    ext
    simp [← HomologicalComplex.comp_f]
  right_inv z := by
    ext
    simp [← HomologicalComplex.comp_f]
  map_add' z z' := by
    ext
    simp

/-- **Changing the target of a Hom complex along an isomorphism.** An isomorphism `e : M ≅ M'`
induces an isomorphism `Hom^•(K, M) ≅ Hom^•(K, M')`, degreewise by postcomposition with `e`. -/
def targetIso (e : M ≅ M') : K.HomComplex M ≅ K.HomComplex M' :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainTargetEquiv K e n).toAddCommGrpIso)
    fun _ m _ => by
      ext z
      exact δ_comp_ofHom z e.hom m

/-- In degree `n`, `targetIso` sends a cochain `z` to its composition with `e.hom`. -/
theorem targetIso_hom_apply (e : M ≅ M') (n : ℤ) (z : Cochain K M n) :
    AddCommGrpCat.Hom.hom ((targetIso K e).hom.f n) z =
      z.comp (Cochain.ofHom e.hom) (add_zero n) :=
  rfl

/-- `targetIso` postcomposes each local component of a cochain with `e`. -/
theorem targetIso_hom_apply_v (e : M ≅ M') (n : ℤ) (z : Cochain K M n)
    (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((targetIso K e).hom.f n) z).v p q hpq =
      z.v p q hpq ≫ e.hom.f q := by
  simp [targetIso_hom_apply]

end CochainComplex.HomComplex

end
