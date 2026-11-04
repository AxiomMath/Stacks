module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftAxiomBIso

/-!
# The identification of axiom (B) for complexes is coherent with the two shift comparisons

For the differential graded category of complexes, the identification of axiom (B) is
`CochainComplex.HomComplex.Cochain.rightShift`, which reindexes the target of a cochain by the
degreewise identifications of `CochainComplex.HomComplex.Cochain.rightShift_v`. It is coherent
with the comparisons `X⟦0⟧ ≅ X` and `X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧` of `CategoryTheory.shiftFunctorZero` and
`CategoryTheory.shiftFunctorAdd`, and the `ℤ`-action data of the translations of `Comp(Comp^dg(B))`
and `K(Comp^dg(B))` are `CochainComplex.dgZeroIso` and `CochainComplex.dgAddIso`.

## Main results

* `CochainComplex.rightShift_zero_comp` and `CochainComplex.rightShift_add_eq`: shifting the
  target of a cochain by `0` is composing with the comparison `X⟦0⟧ ≅ X`, and shifting it by
  `n + m` is shifting by `n` and then by `m`, composed with the comparison
  `X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧`.
* `CochainComplex.rightUnshift_comp_add_eq`: the same identity read for the inverse
  reindexings, with every degree prescribed by an equation rather than by its spelling.
* `CochainComplex.shiftFunctorZero_dgComp_hom_app`,
  `CochainComplex.shiftFunctorAdd_dgComp_hom_app`,
  `CochainComplex.shiftFunctorZero_dgCategoryK_hom_app` and
  `CochainComplex.shiftFunctorAdd_dgCategoryK_hom_app`: the `ℤ`-action data of the two
  translations `CochainComplex.dgCompShift` and `CochainComplex.dgCategoryKShift` are
  `CochainComplex.dgZeroIso` and `CochainComplex.dgAddIso`.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes; [Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF).
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

open CochainComplex.HomComplex

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-! ### The identification of axiom (B) against the two comparisons of objects -/

/-- Shifting the target of a cochain by `0` is composing with the comparison `X⟦0⟧ ≅ X`.
This is the coherence of the identification of axiom (B) with
`CategoryTheory.shiftFunctorZero` for the differential graded category of complexes. -/
theorem rightShift_zero_comp (X z : CochainComplex B ℤ) (i k : ℤ) (hk : i + 0 = k)
    (a : Cochain z (X⟦(0 : ℤ)⟧) i) :
    (a.comp (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app X))
      hk).rightShift 0 i hk = a := by
  ext p q hpq
  obtain rfl : q = p + k := by omega
  rw [Cochain.rightShift_v _ 0 i hk p (p + k) hpq (p + k) (by omega),
    Cochain.comp_v a _ hk p (p + k) (p + k) hpq (by omega), Cochain.ofHom_v,
    shiftFunctorZero_hom_app_f]
  simp [HomologicalComplex.XIsoOfEq]

/-- Shifting the target of a cochain by `n + m` is shifting it by `n` and then by `m`, up to
the comparison `X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧`. This is the coherence of the identification of axiom (B)
with `CategoryTheory.shiftFunctorAdd` for the differential graded category of complexes. -/
theorem rightShift_add_eq (X z : CochainComplex B ℤ) (k n m l : ℤ) (hl : k + 0 = l)
    (f : Cochain z X (k + (n + m))) :
    (f.rightShift (n + m) k rfl).comp
        (Cochain.ofHom
          ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app X))
        hl =
      (f.rightShift n (k + m) (by omega)).rightShift m l (by omega) := by
  ext p q hpq
  obtain rfl : q = p + k := by omega
  rw [Cochain.comp_v (f.rightShift (n + m) k rfl) _ hl p (p + k) (p + k) (by omega) (by omega),
    Cochain.rightShift_v f (n + m) k rfl p (p + k) (by omega) (p + (k + (n + m))) rfl,
    Cochain.rightShift_v _ m l (by omega) p (p + k) hpq (p + (k + m)) (by omega),
    Cochain.rightShift_v f n (k + m) (by omega) p (p + (k + m)) (by omega)
      (p + (k + (n + m))) (by omega),
    Cochain.ofHom_v, shiftFunctorAdd_hom_app_f]
  simp [HomologicalComplex.XIsoOfEq]

/-- `CochainComplex.rightShift_add_eq` for the inverse reindexings: reindexing a degree-`i`
cochain `z ⟶ X⟦n⟧⟦m⟧` back to `z ⟶ X` in two steps is composing with the comparison
`X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧` and reindexing back in one. Every degree is a parameter constrained by an
equation. -/
theorem rightUnshift_comp_add_eq (X z : CochainComplex B ℤ) (n m i i' e d : ℤ)
    (hi' : i + 0 = i') (he : e + n = d) (him : i' + m = e) (hd : i + (n + m) = d)
    (α : Cochain z (X⟦n + m⟧ : CochainComplex B ℤ) i) :
    α.comp (Cochain.ofHom
        ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app X)) hi' =
      ((α.rightUnshift d hd).rightShift n e he).rightShift m i' him := by
  obtain rfl : i' = i := by omega
  obtain rfl : d = i' + (n + m) := hd.symm
  obtain rfl : e = i' + m := by omega
  conv_lhs => rw [← Cochain.rightShift_rightUnshift α (i' + (n + m)) hd]
  exact rightShift_add_eq X z i' n m i' hi' (α.rightUnshift (i' + (n + m)) hd)

/-! ### The `ℤ`-action data of the two induced translations -/

variable (B)

/-- The comparison of the data inducing `CochainComplex.dgCategoryKShift` is an equality of
functors. -/
private theorem compToK_shiftEq (n : ℤ) :
    DGCategory.compToK (dgCategory B) ⋙ (dgShiftFunctor B n).onK =
      (dgShiftFunctor B n).onComp ⋙ DGCategory.compToK (dgCategory B) :=
  (DGCategory.dgFunctor_induces_functors (dgShiftFunctor B n)).2.2.2.2

/-- The comparison of the data inducing `CochainComplex.dgCompShift` is the identity on objects,
so each of its components is an identity. -/
private theorem cochainToComplexShiftEq_hom_app (k : ℤ) (y : CochainComplex B ℤ) :
    (eqToIso (cochainToComplexShiftEq B k)).hom.app y = 𝟙 _ := by
  simp only [eqToIso.hom, eqToHom_app]
  rfl

/-- The inverse components of that comparison are identities too. -/
private theorem cochainToComplexShiftEq_inv_app (k : ℤ) (y : CochainComplex B ℤ) :
    (eqToIso (cochainToComplexShiftEq B k)).inv.app y = 𝟙 _ := by
  simp only [eqToIso.inv, eqToHom_app]
  rfl

/-- A morphism composed with identities on the left, and on the right with an identity followed by
the image of an identity, is itself. -/
private theorem id_comp_id_comp_map_id {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X : E} {Z : D} (f : X ⟶ F.obj Z) : 𝟙 X ≫ f ≫ 𝟙 (F.obj Z) ≫ F.map (𝟙 Z) = f := by simp

/-- The components of the comparison of the data inducing `CochainComplex.dgCategoryKShift`
are identities. -/
private theorem compToK_shiftEq_app (k : ℤ) (y : (dgCategory B).Comp) :
    (eqToIso (compToK_shiftEq B k)).hom.app y = 𝟙 _ ∧
      (eqToIso (compToK_shiftEq B k)).inv.app y = 𝟙 _ :=
  ⟨rfl, rfl⟩

/-- The comparison `X⟦0⟧ ≅ X` of the translation of `Comp(Comp^dg(B))` is
`CochainComplex.dgZeroIso`. -/
theorem shiftFunctorZero_dgComp_hom_app (x : CochainComplex B ℤ) :
    (CategoryTheory.shiftFunctorZero (dgCategory B).Comp ℤ).hom.app x =
      (dgZeroIso B x).hom := by
  refine (CategoryTheory.shiftFunctorZero_hom_app_obj_of_induced
    (cochainToComplexFunctor B) ℤ (fun n => (dgShiftFunctor B n).onComp)
    (fun n => eqToIso (cochainToComplexShiftEq B n)) x).trans ?_
  rw [cochainToComplexShiftEq_hom_app]
  exact Category.id_comp _

/-- The comparison `X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧` of the translation of `Comp(Comp^dg(B))` is
`CochainComplex.dgAddIso`. -/
theorem shiftFunctorAdd_dgComp_hom_app (n m : ℤ) (x : CochainComplex B ℤ) :
    (CategoryTheory.shiftFunctorAdd (dgCategory B).Comp n m).hom.app x =
      (dgAddIso B n m x).hom := by
  refine (CategoryTheory.shiftFunctorAdd_hom_app_obj_of_induced
    (cochainToComplexFunctor B) (fun k => (dgShiftFunctor B k).onComp)
    (fun k => eqToIso (cochainToComplexShiftEq B k)) n m x).trans ?_
  simp only [cochainToComplexShiftEq_hom_app, cochainToComplexShiftEq_inv_app]
  exact id_comp_id_comp_map_id _ _

/-- The comparison `X⟦0⟧ ≅ X` of the translation of `K(Comp^dg(B))` is the homotopy class of
`CochainComplex.dgZeroIso`. -/
theorem shiftFunctorZero_dgCategoryK_hom_app (x : (dgCategory B).K) :
    (CategoryTheory.shiftFunctorZero (dgCategory B).K ℤ).hom.app x =
      Quotient.mk ((dgCategory B).homotopySetoid _ _) (dgZeroIso B x).hom := by
  refine (CategoryTheory.shiftFunctorZero_hom_app_obj_of_induced
    (DGCategory.compToK (dgCategory B)) ℤ (fun n => (dgShiftFunctor B n).onK)
    (fun n => eqToIso (compToK_shiftEq B n)) (DGCategory.kToCompObj x)).trans ?_
  rw [(compToK_shiftEq_app B 0 _).1]
  exact (Category.id_comp _).trans
    (congrArg (fun m => (DGCategory.compToK (dgCategory B)).map m)
      (shiftFunctorZero_dgComp_hom_app B (DGCategory.kToCompObj x)))

/-- The comparison `X⟦n + m⟧ ≅ X⟦n⟧⟦m⟧` of the translation of `K(Comp^dg(B))` is the homotopy
class of `CochainComplex.dgAddIso`. -/
theorem shiftFunctorAdd_dgCategoryK_hom_app (n m : ℤ) (x : (dgCategory B).K) :
    (CategoryTheory.shiftFunctorAdd (dgCategory B).K n m).hom.app x =
      Quotient.mk ((dgCategory B).homotopySetoid _ _) (dgAddIso B n m x).hom := by
  refine (CategoryTheory.shiftFunctorAdd_hom_app_obj_of_induced
    (DGCategory.compToK (dgCategory B)) (fun k => (dgShiftFunctor B k).onK)
    (fun k => eqToIso (compToK_shiftEq B k)) n m (DGCategory.kToCompObj x)).trans ?_
  simp only [(compToK_shiftEq_app B _ _).1, (compToK_shiftEq_app B _ _).2]
  exact (id_comp_id_comp_map_id _ _).trans
    (congrArg (fun t => (DGCategory.compToK (dgCategory B)).map t)
      (shiftFunctorAdd_dgComp_hom_app B n m (DGCategory.kToCompObj x)))

end CochainComplex

end
