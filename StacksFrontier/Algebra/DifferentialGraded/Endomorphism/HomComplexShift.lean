module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.RightAction
public import StacksFrontier.Homology.HomComplex.ShiftHom

/-!
# Shifting a Hom complex is a map of differential graded modules

Let `R` be a commutative ring, let `A` be a differential graded `R`-algebra, let `M` and `N` be
cochain complexes of `R`-modules and let `a b : ℤ`. The canonical identification
`Hom^•(M, N)[a - b] ≅ Hom^•(M[b], N[a])` of Tag 0FNN is a map of right, resp. left, differential
graded `A`-modules as soon as `M` carries the structure of a left, resp. right, differential graded
`A`-module. Remark 22.26.9 is the case `a = 0`, `b = k`, where the identification reads
`Hom^•(M, N)[-k] ⟶ Hom^•(M[k], N)`.

## Main definitions

* `CochainComplex.HomComplex.Cochain.reindexShift`: the evident reindexing of a homogeneous cochain
  along the shifts of its source and target by possibly different amounts.
* `CochainComplex.HomComplex.shiftHomCochain`: the degreewise map underlying the identification of
  Tag 0FNN.

## Main results

* `DifferentialGradedAlgebra.LeftAction.shiftHomCochain_comp`: the left-module clause of
  Remark 22.26.9. Both `Hom^•(M, N)[a - b]` and `Hom^•(M[b], N[a])` are right differential graded
  `A`-modules, by precomposition, and the identification is `A`-linear.
* `DifferentialGradedAlgebra.RightAction.shiftHomCochain_homAction`: the right-module clause, for
  the left actions induced on the two Hom complexes.
* `CochainComplex.HomComplex.shiftHomCochain_comp`: the sign of both clauses, for an arbitrary
  homogeneous endomorphism of `M` and with no differential graded algebra in sight.
* `CochainComplex.HomComplex.Cochain.reindexShift_comp`: the sign-free core, namely that
  reindexing is compatible with precomposition.

## Implementation notes

*The map is the one bundled by Tag 0FNN.* `CochainComplex.HomComplex.homComplexShiftIso` comes
with its degreewise description, and `shiftHomCochain` is the map the first conjunct of that
description computes, namely `(-1)^(n b)` times `reindexShift` in degree `n`
(`shiftHomCochain_eq`). Since Tag 0FNN already provides the isomorphism of complexes, the content
of Remark 22.26.9 is exactly the `A`-linearity stated by the two main theorems.

*The sign of each module structure is forced.* If `M` is a left module then `Hom^•(M, N)` is a
right module by precomposition, without signs, and shifting a right module introduces no sign
either, so the same formula describes the action on `Hom^•(M, N)[a - b]`; the shift `M[b]` of a
left module carries the Koszul factor `(-1)^(p b)`, which is
`DifferentialGradedAlgebra.LeftAction.shift`. If `M` is a right module then `Hom^•(M, N)` is a
left module and a sign is unavoidable: a degree-`p` element acts on a degree-`q` cochain by
`(-1)^(p q)` times precomposition with the signed right action, and shifting that left module by
`a - b` introduces the further Koszul factor `(-1)^(p (a - b))`. With those conventions both
clauses reduce to `Cochain.reindexShift_comp`, which carries no sign at all: the factor
`(-1)^(n b)` of `shiftHomCochain` changes by exactly the Koszul factor of the shifted module.

*Universes are independent where the mathematics allows it.* The reindexing and its lemmas hold
for cochain complexes in an arbitrary preadditive category, and `shiftHomCochain` for complexes of
`R`-modules in an arbitrary universe. The two clauses of the remark are tied to module universe
`u` by `DifferentialGradedAlgebra.LeftAction`.

## References

* [Stacks Project, Tag 0FQ9](https://stacks.math.columbia.edu/tag/0FQ9)
* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v w

variable {R : Type u} [CommRing R]

namespace CochainComplex.HomComplex

namespace Cochain

variable {C : Type*} [Category C] [Preadditive C]

/-- The evident reindexing of a homogeneous cochain along the shifts of its source and target: the
`(p, q)`-component of `reindexShift M N a b n z` is the `(p + b, q + a)`-component of `z`,
conjugated by the canonical identifications of the terms of a shifted complex. -/
def reindexShift (M N : CochainComplex C ℤ) (a b n : ℤ) (z : Cochain M N n) :
    Cochain (M⟦b⟧) (N⟦a⟧) (n + (b - a)) :=
  Cochain.mk fun p q _ =>
    (M.shiftFunctorObjXIso b p (p + b) rfl).hom ≫
      z.v (p + b) (q + a) (by omega) ≫ (N.shiftFunctorObjXIso a q (q + a) rfl).inv

/-- The homogeneous components of the reindexing. -/
theorem reindexShift_v (M N : CochainComplex C ℤ) (a b n p q : ℤ)
    (hpq : p + (n + (b - a)) = q) (z : Cochain M N n) :
    (reindexShift M N a b n z).v p q hpq =
      (M.shiftFunctorObjXIso b p (p + b) rfl).hom ≫
        z.v (p + b) (q + a) (by omega) ≫ (N.shiftFunctorObjXIso a q (q + a) rfl).inv :=
  rfl

/-- Reindexing is compatible with precomposition. This is the sign-free core of both clauses of
Remark 22.26.9 of the Stacks project. -/
theorem reindexShift_comp (M N : CochainComplex C ℤ) (a b p q : ℤ)
    (w : Cochain M M p) (z : Cochain M N q) :
    reindexShift M N a b (p + q) (w.comp z rfl) =
      (w.shift b).comp (reindexShift M N a b q z) (by omega) := by
  refine Cochain.ext _ _ fun s u hsu => ?_
  rw [Cochain.comp_v _ _ (show p + (q + (b - a)) = p + q + (b - a) by omega) s (s + p) u
      (by omega) (by omega),
    Cochain.shift_v w b s (s + p) rfl (s + b) (s + p + b) rfl (by omega)]
  simp only [reindexShift_v,
    Cochain.comp_v w z rfl (s + b) (s + p + b) (u + a) (by omega) (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Reindexing commutes with multiplication by a sign. -/
theorem reindexShift_units_smul {S : Type*} [Ring S] [Linear S C] (M N : CochainComplex C ℤ)
    (a b n : ℤ) (k : Sˣ) (z : Cochain M N n) :
    reindexShift M N a b n (k • z) = k • reindexShift M N a b n z := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.units_smul_v, reindexShift_v, reindexShift_v, Cochain.units_smul_v]
  simp only [Units.smul_def, Linear.comp_smul, Linear.smul_comp]

end Cochain

/-- **Stacks 0FNN**, read on homogeneous cochains: the degreewise map underlying the canonical
identification `Hom^•(M, N)[a - b] ≅ Hom^•(M[b], N[a])`, transported into a morphism of complexes
`Hom^•(M, N) ⟶ Hom^•(M[b], N[a])[b - a]`. For `a = 0` and `b = k` this is the map
`Hom^•(M, N)[-k] ⟶ Hom^•(M[k], N)` of Remark 22.26.9. -/
noncomputable def shiftHomCochain (M N : CochainComplex (ModuleCat.{w} R) ℤ) (a b n : ℤ)
    (z : Cochain M N n) : Cochain (M⟦b⟧) (N⟦a⟧) (n + (b - a)) :=
  ((HomComplexR R (M⟦b⟧) (N⟦a⟧)).shiftFunctorObjXIso (b - a) n (n + (b - a)) rfl).hom.hom
    ((((shiftFunctorCompIsoId (CochainComplex (ModuleCat.{w} R) ℤ) (a - b) (b - a)
          (by omega)).inv.app (HomComplexR R M N) ≫
        (homComplexShiftIso R M N a b).1.hom⟦b - a⟧').f n).hom z)

/-- In degree `n` the identification of Tag 0FNN is the sign `(-1)^(n b)` times the evident
reindexing. -/
theorem shiftHomCochain_eq (M N : CochainComplex (ModuleCat.{w} R) ℤ) (a b n : ℤ)
    (z : Cochain M N n) :
    shiftHomCochain M N a b n z = (n * b).negOnePow • Cochain.reindexShift M N a b n z :=
  (homComplexShiftIso R M N a b).2.1 n z

/-- The identification of Tag 0FNN commutes with multiplication by a sign. -/
theorem shiftHomCochain_units_smul (M N : CochainComplex (ModuleCat.{w} R) ℤ) (a b n : ℤ)
    (k : ℤˣ) (z : Cochain M N n) :
    shiftHomCochain M N a b n (k • z) = k • shiftHomCochain M N a b n z := by
  rw [shiftHomCochain_eq, shiftHomCochain_eq, Cochain.reindexShift_units_smul, smul_comm]

/-- Two signs agree as soon as their exponents differ by an even integer. -/
private theorem negOnePow_congr {x y c : ℤ} (h : x = y + 2 * c) : x.negOnePow = y.negOnePow := by
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- The identification of Tag 0FNN turns precomposition with a homogeneous endomorphism `w` of `M`
into precomposition with the shift of `w`, up to the sign `(-1)^(p b)` in which the two clauses of
Remark 22.26.9 differ. -/
theorem shiftHomCochain_comp (M N : CochainComplex (ModuleCat.{w} R) ℤ) (a b p q : ℤ)
    (w : Cochain M M p) (z : Cochain M N q) :
    shiftHomCochain M N a b (p + q) (w.comp z rfl) =
      (p * b).negOnePow • (w.shift b).comp (shiftHomCochain M N a b q z) (by omega) := by
  have hs : (p + q) * b = p * b + q * b := by ring
  rw [shiftHomCochain_eq, shiftHomCochain_eq, Cochain.comp_units_smul, smul_smul,
    ← Int.negOnePow_add, Cochain.reindexShift_comp, hs]

end CochainComplex.HomComplex

namespace DifferentialGradedAlgebra

variable {A : DifferentialGradedAlgebra.{u, v} R} {M N : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **Stacks 0FQ9**, left modules. If `M` is a left differential graded `A`-module then the
identification `Hom^•(M, N)[a - b] ≅ Hom^•(M[b], N[a])` of Tag 0FNN is a map of right differential
graded `A`-modules: both actions are precomposition, on the source with the given action — shifting
a right module introduces no sign — and on the target with the Koszul-signed shifted action
`DifferentialGradedAlgebra.LeftAction.shift`. Remark 22.26.9 is the case `a = 0`, `b = k`. -/
@[stacks 0FQ9 "left modules"]
theorem LeftAction.shiftHomCochain_comp (act : A.LeftAction M) (a b p q : ℤ) (α : A.grading p)
    (z : Cochain M N q) :
    shiftHomCochain M N a b (p + q) ((act.action p α).comp z rfl) =
      ((act.shift b).action p α).comp (shiftHomCochain M N a b q z) (by omega) := by
  rw [HomComplex.shiftHomCochain_comp, LeftAction.shift_action, Cochain.units_smul_comp]

/-- **Stacks 0FQ9**, right modules. If `M` is a right differential graded `A`-module then the
identification `Hom^•(M, N)[a - b] ≅ Hom^•(M[b], N[a])` of Tag 0FNN is a map of left differential
graded `A`-modules: the target carries the left action induced by the shifted right action on
`M[b]`, and the source carries the left action induced on `Hom^•(M, N)`, multiplied by the Koszul
factor `(-1)^(p (a - b))` of the shift by `a - b`. Remark 22.26.9 is the case `a = 0`, `b = k`,
where that factor is `(-1)^(p k)`. -/
@[stacks 0FQ9 "right modules"]
theorem RightAction.shiftHomCochain_homAction (t : A.RightAction M) (a b p q : ℤ)
    (α : A.grading p) (z : Cochain M N q) :
    shiftHomCochain M N a b (p + q)
        ((p * (a - b)).negOnePow • (t.homLeftAction N).homAction p q (p + q) (by omega) α z) =
      ((t.shift b).homLeftAction (N⟦a⟧)).homAction p (q + (b - a)) (p + q + (b - a)) (by omega) α
        (shiftHomCochain M N a b q z) := by
  rw [RightAction.homLeftAction_homAction, RightAction.homLeftAction_homAction,
    shiftHomCochain_units_smul, shiftHomCochain_units_smul, HomComplex.shiftHomCochain_comp,
    RightAction.shift_action, Cochain.units_smul_comp]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  exact negOnePow_congr (c := p * a - p * b) (by ring)

end DifferentialGradedAlgebra
