module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# The target shift of a Hom complex

Let `K` and `L` be cochain complexes in a preadditive category. Shifting the target by `a`
identifies the `a`-shift of the Hom complex with the Hom complex into the shift,
`Hom^•(K, L)[a] ≅ Hom^•(K, L[a])`, degreewise by Mathlib's
`CochainComplex.HomComplex.Cochain.rightShift`.

## Main definitions

* `CochainComplex.HomComplex.homComplexTargetShiftIso`: the identification
  `Hom^•(K, L)[a] ≅ Hom^•(K, L[a])`.

## Main results

* `CochainComplex.HomComplex.homComplexTargetShiftIso_hom_f_apply` and
  `CochainComplex.HomComplex.homComplexTargetShiftIso_hom_f_apply_v`: the identification is
  `CochainComplex.HomComplex.Cochain.rightShift`, whose homogeneous components are the evident
  reindexing with **no sign**.

## Implementation notes

*No sign appears.* `CochainComplex.HomComplex.Cochain.rightShift` reindexes homogeneous
components without a sign, and by `CochainComplex.HomComplex.Cochain.δ_rightShift` it multiplies
the Hom-complex differential by `(-1)^a` — which is exactly the sign by which the differential of
an `a`-shifted complex differs from the original. So the reindexing is already a morphism of
complexes and needs no correction; this is the half of the two-sided shift identification of a
Hom complex that carries no Koszul sign. (The sign-bearing half is the shift of the *source*; the
two-sided identification over a commutative ring is
`CochainComplex.HomComplex.homComplexShiftIso` of
`StacksFrontier.Homology.HomComplex.ShiftHom`, Tag 0FNN.)

The target category is only assumed preadditive, so the sign `(-1)^a` acts through the `ℤˣ`-action
on cochains rather than through an `R`-linear structure; `Cochain.rightShift_units_smul` of
Mathlib is stated for a linear category, so the additivity needed here is taken from
`CochainComplex.HomComplex.Cochain.rightShiftAddEquiv` instead.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Shifting the target of a cochain commutes with multiplication by a unit integer. This is
`CochainComplex.HomComplex.Cochain.rightShift_units_smul` without the linearity hypothesis:
the `ℤˣ`-action is the `ℤ`-action, under which `rightShiftAddEquiv` is a map of modules. -/
private lemma rightShift_units_smul {K L : CochainComplex C ℤ} {n : ℤ} (γ : Cochain K L n)
    (a n' : ℤ) (hn' : n' + a = n) (ε : ℤˣ) :
    (ε • γ).rightShift a n' hn' = ε • γ.rightShift a n' hn' :=
  map_zsmul (Cochain.rightShiftAddEquiv K L n a n' hn') (ε : ℤ) γ

/-- **The target shift of a Hom complex.** For cochain complexes `K` and `L` in a preadditive
category and `a : ℤ`, the `a`-shift of the Hom complex is the Hom complex into the `a`-shift of
the target, `Hom^•(K, L)[a] ≅ Hom^•(K, L[a])`.

In degree `n` this is `CochainComplex.HomComplex.Cochain.rightShift`, the sign-free reindexing
`Cochain K L (n + a) ≃+ Cochain K (L[a]) n`; it commutes with the differentials because the sign
`(-1)^a` it introduces on `δ` is the one carried by the differential of the shifted complex. -/
def homComplexTargetShiftIso (K L : CochainComplex C ℤ) (a : ℤ) :
    (K.HomComplex L)⟦a⟧ ≅ K.HomComplex (L⟦a⟧) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => addEquivIsoAddCommGroupIso.hom
      (Cochain.rightShiftAddEquiv K L (n + a) a n rfl))
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      ext γ
      change δ i (i + 1) ((show Cochain K L (i + a) from γ).rightShift a i rfl) =
        (a.negOnePow • δ (i + a) (i + 1 + a) (show Cochain K L (i + a) from γ)).rightShift
          a (i + 1) rfl
      rw [Cochain.δ_rightShift _ a i (i + 1) rfl (i + 1 + a) rfl]
      exact (rightShift_units_smul _ a (i + 1) rfl a.negOnePow).symm)

/-- The target shift of a Hom complex is `CochainComplex.HomComplex.Cochain.rightShift` in each
degree. -/
lemma homComplexTargetShiftIso_hom_f_apply (K L : CochainComplex C ℤ) (a n : ℤ)
    (γ : Cochain K L (n + a)) :
    AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L a).hom.f n) γ =
      γ.rightShift a n rfl := rfl

/-- The homogeneous components of the target shift of a Hom complex: the evident reindexing,
with no sign. -/
lemma homComplexTargetShiftIso_hom_f_apply_v (K L : CochainComplex C ℤ) (a n : ℤ)
    (γ : Cochain K L (n + a)) (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L a).hom.f n) γ).v p q hpq =
      γ.v p (q + a) (by omega) ≫ (L.shiftFunctorObjXIso a q (q + a) rfl).inv :=
  Cochain.rightShift_v _ a n rfl p q hpq (q + a) (by omega)

/-- The inverse of the target shift of a Hom complex is
`CochainComplex.HomComplex.Cochain.rightUnshift` in each degree. -/
lemma homComplexTargetShiftIso_inv_f_apply (K L : CochainComplex C ℤ) (a n : ℤ)
    (γ : Cochain K (L⟦a⟧) n) :
    AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L a).inv.f n) γ =
      γ.rightUnshift (n + a) rfl := rfl

end CochainComplex.HomComplex

end
