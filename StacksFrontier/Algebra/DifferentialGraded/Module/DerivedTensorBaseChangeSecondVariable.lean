module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeRegularBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleCoproduct
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBaseChangeFirstVariable
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorQuasiIsoDevissage

/-! # The dévissage of Stacks 0BZ5 in the second variable, and Stacks 0BZ5

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`.
The proof of Stacks 0BZ5 derives the hypothesis of Stacks 0BZ3 for a pair of bimodules with
property (P) from the single instance of it supplied by Stacks 0BZ4, by two dévissages. The first,
in the bimodule `P` over `(A, B)`, is
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_rightModule_of_propertyP`. This
file carries out the second, in the bimodule `P'` over `(B, C)`, and assembles the two.

The dévissage in the second variable runs over the property-(P) filtration of the right
differential graded `Bᵒᵖ ⊗_R C`-module that `P'` is by Tag 0FQJ. Its graded pieces are direct sums
of shifts of the regular module, which as a bimodule is `{}_B(B ⊗_R C)_C`
(`DifferentialGraded.Bimodule.baseChangeRegularBimoduleIso`), and that is where the hypothesis is
spent. The statement being propagated cannot be read off the derived category — the comparison of
Tag 0BZ2 lands in the *ordinary* tensor product, which is not a functor on `D(C, d)` — so it is
propagated in the equivalent form supplied by
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_iff_quasiIso`: the ordinary
tensor product of a fixed left-orthogonal resolution is a quasi-isomorphism. In that form the
three closure clauses are exactly that `W ⊗_B -` commutes with direct sums and with the
translation in the bimodule variable and carries an admissible short exact sequence of bimodules
to one.

## Main definitions

* `DifferentialGraded.Bimodule.tensorModuleNatIso`: tensoring with an isomorphism of bimodules.
* `DifferentialGraded.Bimodule.tensorBimoduleDerivedNatTrans`: the morphism of functors on
  modules over `Bᵒᵖ ⊗_R C` whose invertibility the dévissage propagates.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfBaseChange`: Stacks 0BZ5 with its own
  hypothesis, Tag 0BZ4, as the only input.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra`: **the second
  conclusion of Stacks 09S4**, the conclusion of Tag 0BZ5 with K-flatness of `C` as a complex of
  `R`-modules as the only hypothesis.

## Main results

* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_second_propertyP`: **the
  dévissage of Stacks 0BZ5 in the second variable.**
* `DifferentialGraded.Bimodule.baseChangeDevissage`: the dévissage of Stacks 0BZ5, which is the
  hypothesis `DifferentialGraded.Bimodule.BaseChangeDevissage` of
  `DifferentialGraded.Bimodule.derivedTensorFunctorCompIso`.

## Implementation notes

*Why the property is stated in `D(C, d)` and the two short exact sequence clauses are not.*
Invariance under isomorphism and the direct sum clause are instances of the generic dévissage
lemmas for a morphism of functors, which need the target to be a category where the colimit is
preserved; the localization `D(C, d)` is that category, so the property is stated as
invertibility of the component of the localized transformation. An admissible short exact
sequence of bimodules, on the other hand, is carried by the ordinary tensor product to an
admissible short exact sequence, and the propagation along it is the five lemma applied to the
long exact cohomology ladder, which is
`DifferentialGradedModule.quasiIso_natTrans_app_of_isAdmissibleShortExact`, so those two clauses
are run through the equivalent quasi-isomorphism form.

*No direct sums, shifts or exact sequences of bimodules are constructed.* The induction runs over
right differential graded `Bᵒᵖ ⊗_R C`-modules, where all three constructions already exist; only
their images under `W ⊗_B -` are compared, which is what
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorBimoduleCoproduct.lean`,
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorBimoduleShift.lean` and
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorAdmissible.lean` do.

## References

* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5); the dévissage is in its
  proof.
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change
  comparison, which is the hypothesis.
* [Stacks Project, Tag 09S4](https://stacks.math.columbia.edu/tag/09S4), which discharges that
  hypothesis when `C` is K-flat as a complex of `R`-modules.
* [Stacks Project, Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3), the composition of
  derived tensor functors.
* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2), the comparison from the
  derived to the ordinary tensor product.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules over
  the graded tensor product.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra StacksDraft.NatTransDevissage

variable {R : Type u} [CommRing R]

/-! ### Tensoring with an isomorphism of bimodules -/

section BimoduleIso

variable {B C : DifferentialGradedAlgebra.{u, u} R}

/-- **Tensoring with an isomorphism of bimodules is an isomorphism of the ordinary tensor
functors.** Both directions are the transformation of Tag 09S3, and they compose to the identity
because that transformation is functorial in the bimodule. -/
def tensorModuleNatIso {N N' : Bimodule B C} (e : N ≅ N') :
    tensorCompFunctor N ≅ tensorCompFunctor N' where
  hom := tensorModuleNatTrans e.hom
  inv := tensorModuleNatTrans e.inv
  hom_inv_id := by rw [← tensorModuleNatTrans_comp, e.hom_inv_id, tensorModuleNatTrans_id]
  inv_hom_id := by rw [← tensorModuleNatTrans_comp, e.inv_hom_id, tensorModuleNatTrans_id]

/-- **Whether the ordinary tensor product of a homomorphism is a quasi-isomorphism only depends
on the isomorphism class of the bimodule.** -/
theorem quasiIso_tensorCompFunctor_map_iff_of_iso {N N' : Bimodule B C} (e : N ≅ N')
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W') :
    QuasiIso ((forgetToCochainComplex C).map ((tensorCompFunctor N).map ρ)) ↔
      QuasiIso ((forgetToCochainComplex C).map ((tensorCompFunctor N').map ρ)) := by
  rw [← isIso_q_map_toHomotopyCategory_map_iff C ((tensorCompFunctor N).map ρ),
    ← isIso_q_map_toHomotopyCategory_map_iff C ((tensorCompFunctor N').map ρ)]
  exact NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (tensorModuleNatIso e)
      (toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q)) ρ

end BimoduleIso

/-! ### The transformation whose invertibility is propagated -/

section Devissage

variable (B C : DifferentialGradedAlgebra.{u, u} R)

/-- **The morphism of functors on right differential graded `Bᵒᵖ ⊗_R C`-modules whose
invertibility the dévissage in the second variable propagates**: the ordinary tensor product of
`ρ : W ⟶ W'`, read in `D(C, d)`. -/
def tensorBimoduleDerivedNatTrans {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W') :
    tensorBimoduleFunctor B C W ⋙ toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q ⟶
      tensorBimoduleFunctor B C W' ⋙ toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q :=
  Functor.whiskerRight (tensorBimoduleNatTrans B C ρ)
    (toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q)

/-- The component of the localized transformation is invertible exactly when the ordinary tensor
product of `ρ` is a quasi-isomorphism. -/
theorem isIso_tensorBimoduleDerivedNatTrans_app_iff
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app Y) ↔
      QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Y)) :=
  isIso_q_map_toHomotopyCategory_map_iff C ((tensorBimoduleNatTrans B C ρ).app Y)

/-! ### The four closure clauses -/

/-- The localized ordinary tensor functor preserves the direct sum of a family of right
differential graded `Bᵒᵖ ⊗_R C`-modules: the ordinary tensor functor does, and so does the
passage to `D(C, d)`. -/
theorem preservesColimit_tensorBimoduleDerived (W : DifferentialGradedModule.{u, u, u} B)
    {ι : Type u} (Y : ι → DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    PreservesColimit (Discrete.functor Y)
      (tensorBimoduleFunctor B C W ⋙ toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q) := by
  have := preservesColimit_tensorBimoduleFunctor B C W Y
  have : PreservesColimit (Discrete.functor Y ⋙ tensorBimoduleFunctor B C W)
      (toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q) := inferInstance
  infer_instance

/-- **The direct sum clause.** -/
theorem isIso_tensorBimoduleDerivedNatTrans_app_directSumObj
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    {ι : Type u} [DecidableEq ι]
    (Y : ι → DifferentialGradedModule.{u, u, u} (tensorAlgebra B C))
    (h : ∀ i, IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app (Y i))) :
    IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app (directSumObj Y)) := by
  have := preservesColimit_tensorBimoduleDerived B C W Y
  have := preservesColimit_tensorBimoduleDerived B C W' Y
  exact isIso_app_of_isColimit (tensorBimoduleDerivedNatTrans B C ρ) (Discrete.functor Y)
    (isColimit_directSumObj Y) (fun j => h j.as)

/-- **The translation clause.** The comparison of
`DifferentialGraded.Bimodule.tensorBimoduleShiftIso` is natural in the module variable, so the
ordinary tensor product of `ρ` at `Y[k]` is, up to isomorphisms, the translation of the ordinary
tensor product of `ρ` at `Y`. -/
theorem quasiIso_tensorBimoduleNatTrans_app_shift
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) (k : ℤ)
    (h : QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Y))) :
    QuasiIso ((forgetToCochainComplex C).map
      ((tensorBimoduleNatTrans B C ρ).app (DifferentialGradedModule.shift Y k))) := by
  have hs := quasiIso_forget_shiftFunctor_map ((tensorBimoduleNatTrans B C ρ).app Y) k h
  have hiW' : IsIso ((forgetToCochainComplex C).map
    (tensorBimoduleShiftIso B C W' Y k).hom) := inferInstance
  have h2 : QuasiIso ((forgetToCochainComplex C).map
        ((tensorBimoduleNatTrans B C ρ).app (DifferentialGradedModule.shift Y k)) ≫
      (forgetToCochainComplex C).map (tensorBimoduleShiftIso B C W' Y k).hom) := by
    rw [← Functor.map_comp (forgetToCochainComplex C),
      tensorBimoduleShiftIso_naturality B C ρ Y k,
      Functor.map_comp (forgetToCochainComplex C), quasiIso_iff_comp_left]
    exact hs
  exact (quasiIso_iff_comp_right _
    ((forgetToCochainComplex C).map (tensorBimoduleShiftIso B C W' Y k).hom)).1 h2

/-- **The two admissible short exact sequence clauses.** The ordinary tensor product carries an
admissible short exact sequence of right differential graded `Bᵒᵖ ⊗_R C`-modules to an admissible
short exact sequence, and the five lemma applies to the resulting long exact cohomology ladder. -/
theorem quasiIso_tensorBimoduleNatTrans_app_of_isAdmissibleShortExact
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    {X Y Z : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hip : DifferentialGradedModule.IsAdmissibleShortExact i p) :
    (QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app X)) →
        QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Y)) →
        QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Z))) ∧
      (QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app X)) →
        QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Z)) →
        QuasiIso ((forgetToCochainComplex C).map ((tensorBimoduleNatTrans B C ρ).app Y))) :=
  quasiIso_natTrans_app_of_isAdmissibleShortExact C (tensorBimoduleNatTrans B C ρ) i p
    (isAdmissibleShortExact_tensorBimoduleFunctor_map B C W i p hip)
    (isAdmissibleShortExact_tensorBimoduleFunctor_map B C W' i p hip)

/-! ### The dévissage in the second variable -/

/-- **The dévissage of Stacks 0BZ5 in the second variable, in the quasi-isomorphism form.** If
the ordinary tensor product of `ρ : W ⟶ W'` with `{}_B(B ⊗_R C)_C` is a quasi-isomorphism, then so
is its ordinary tensor product with the bimodule attached to any right differential graded
`Bᵒᵖ ⊗_R C`-module carrying a property-(P) filtration.

The graded pieces of the filtration are direct sums of shifts of the regular module, which as a
bimodule is `{}_B(B ⊗_R C)_C`, so the hypothesis is exactly what the cell clause of the induction
asks for. -/
theorem isIso_tensorBimoduleDerivedNatTrans_app_of_propertyP
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (hbase : IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app
      (regularModule (tensorAlgebra B C))))
    {Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (F : PropertyPFiltration Y) :
    IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app Y) := by
  classical
  have e := isIso_tensorBimoduleDerivedNatTrans_app_iff B C ρ
  refine propertyPFiltration_induction
    (fun Z => IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app Z))
    (fun e h => isIso_app_of_iso (tensorBimoduleDerivedNatTrans B C ρ) e h)
    (fun ι dec k => ?_) (fun N hN => ?_) (fun i p hip hK hM => ?_) (fun i p hip hK hL => ?_) F
  · refine isIso_app_of_iso (tensorBimoduleDerivedNatTrans B C ρ)
      (directSumObjIsoDirectSumShifts (tensorAlgebra B C) k) ?_
    exact isIso_tensorBimoduleDerivedNatTrans_app_directSumObj B C ρ
      (fun i => DifferentialGradedModule.shift (regularModule (tensorAlgebra B C)) (k i))
      (fun i => (e _).2 (quasiIso_tensorBimoduleNatTrans_app_shift B C ρ
        (regularModule (tensorAlgebra B C)) (k i) ((e _).1 hbase)))
  · exact isIso_tensorBimoduleDerivedNatTrans_app_directSumObj B C ρ
      (fun j : ULift.{u} ℕ => N j.down) (fun j => hN j.down)
  · exact (e _).2 ((quasiIso_tensorBimoduleNatTrans_app_of_isAdmissibleShortExact B C ρ i p hip).2
      ((e _).1 hK) ((e _).1 hM))
  · exact (e _).2 ((quasiIso_tensorBimoduleNatTrans_app_of_isAdmissibleShortExact B C ρ i p hip).1
      ((e _).1 hK) ((e _).1 hL))

/-- **The dévissage of Stacks 0BZ5 in the second variable.** If the comparison of Tag 0BZ2 from
the derived to the ordinary tensor product with `{}_B(B ⊗_R C)_C` is invertible at a right
differential graded `B`-module `M`, then the comparison with every differential graded
`(B, C)`-bimodule `P'` having property (P) is invertible at `M`.

Both statements are turned into statements about the ordinary tensor product of one fixed
resolution `ρ : W ⟶ M` by a module orthogonal on the left to the acyclic modules, by
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_iff_quasiIso`; in that form the
dévissage is
`DifferentialGraded.Bimodule.isIso_tensorBimoduleDerivedNatTrans_app_of_propertyP`. -/
theorem isIso_derivedTensorFunctorCounit_app_of_second_propertyP
    (M : DifferentialGradedModule.{u, u, u} B) (P' : Bimodule B C)
    (hbase : IsIso ((derivedTensorFunctorCounit (baseChangeBimodule B C)).app
      ((toHomotopyCategory B).obj M)))
    (hP' : Nonempty (PropertyPFiltration (toTensorModule B C P'))) :
    IsIso ((derivedTensorFunctorCounit P').app ((toHomotopyCategory B).obj M)) := by
  obtain ⟨W, ρ, hρ, hW⟩ := exists_quasiIso_leftOrthogonal_acyclic B M
  have hreg : IsIso ((tensorBimoduleDerivedNatTrans B C ρ).app
      (regularModule (tensorAlgebra B C))) :=
    (isIso_tensorBimoduleDerivedNatTrans_app_iff B C ρ _).2
      ((quasiIso_tensorCompFunctor_map_iff_of_iso (baseChangeRegularBimoduleIso B C).symm ρ).1
        ((isIso_derivedTensorFunctorCounit_app_iff_quasiIso (baseChangeBimodule B C) ρ hρ hW).1
          hbase))
  refine (isIso_derivedTensorFunctorCounit_app_iff_quasiIso P' ρ hρ hW).2 ?_
  refine (quasiIso_tensorCompFunctor_map_iff_of_iso
    (ofTensorModuleToTensorModuleIso B C P') ρ).1 ?_
  exact (isIso_tensorBimoduleDerivedNatTrans_app_iff B C ρ _).1
    (isIso_tensorBimoduleDerivedNatTrans_app_of_propertyP B C ρ hreg hP'.some)

end Devissage

/-! ### The dévissage of Stacks 0BZ5, and Stacks 0BZ5 -/

section Assembly

variable (A B C : DifferentialGradedAlgebra.{u, u} R)

/-- **The dévissage carried out in the proof of Stacks 0BZ5.** If the hypothesis of Tag 0BZ3 holds
for the base-change pair, then it holds for every pair of a differential graded `(A, B)`-bimodule
and a differential graded `(B, C)`-bimodule having property (P).

The dévissage in the second variable carries the hypothesis from `{}_B(B ⊗_R C)_C` to `P'` at the
base-change module `(A ⊗_R B)_B`; the dévissage in the first variable then carries it from
`(A ⊗_R B)_B` to `P_B`. -/
theorem baseChangeDevissage : BaseChangeDevissage A B C := by
  intro hbase P P' hP hP'
  exact isIso_derivedTensorFunctorCounit_app_rightModule_of_propertyP P'
    (isIso_derivedTensorFunctorCounit_app_of_second_propertyP B C (baseChangeModule A B) P'
      hbase hP') P hP

/-- **Stacks 0BZ5 with Tag 0BZ4 as its only hypothesis.** For differential graded algebras
`(A, d)`, `(B, d)` and `(C, d)` over `R` such that the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is an isomorphism, the
composite of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for the differential
graded `(A, C)`-bimodule `N'' = Ñ ⊗_B Ñ'` of the source.

This is `DifferentialGraded.Bimodule.derivedTensorFunctorCompIso` with all four of its remaining
inputs supplied: the second assertion of Tag 09S3 twice, Tag 0BZ3, and the dévissage of the
present proof. -/
@[stacks 0BZ5 "the composite of the two derived tensor functors is the derived tensor functor of \
the composite bimodule, under the Tag 0BZ4 isomorphism that the source itself assumes"]
def derivedTensorFunctorCompIsoOfBaseChange
    (hiso : IsIso (derivedTensorBaseChangeComparison A B C))
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIso (quasiIsoInvertsDerivedTensor A B)
    (quasiIsoInvertsDerivedTensor B C)
    (fun N₀ N₀' h => derivedTensorFunctorCompTensorIso N₀ N₀' h)
    (baseChangeDevissage A B C) hiso N N'

/-- **Stacks Tag 09S4, second conclusion.** *"Let `R` be a ring. Let `(A, d)`, `(B, d)`, `(C, d)`
be differential graded `R`-algebras. If `C` is K-flat as a complex of `R`-modules, then (0BZ4) is
an isomorphism and the conclusion of Lemma 0BZ5 is valid."* This is the second half: if `C` is
K-flat as a complex of `R`-modules, then for every differential graded `(A, B)`-bimodule `N` and
every differential graded `(B, C)`-bimodule `N'` the composite of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'`
is isomorphic to `- ⊗_A^𝐋 N''` for the differential graded `(A, C)`-bimodule
`N'' = Ñ ⊗_B Ñ'` of `DifferentialGraded.Bimodule.compTensorResolution`, which is the conclusion
of Tag 0BZ5.

K-flatness of `C` is the only hypothesis, exactly as in the source. The first half of the tag,
`DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_of_kFlat`, supplies the sole
hypothesis of Tag 0BZ5 in the form
`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfBaseChange`, whose own four inputs are
discharged there by the second assertion of Tag 09S3 twice, Tag 0BZ3 and the dévissage above. -/
@[stacks 09S4 "the conclusion of Stacks 0BZ5 is valid when C is K-flat as a complex of \
R-modules"]
def derivedTensorFunctorCompIsoOfKFlatAlgebra
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIsoOfBaseChange A B C
    (isIso_derivedTensorBaseChangeComparison_of_kFlat A B C hC) N N'

end Assembly

end DifferentialGraded.Bimodule

end
