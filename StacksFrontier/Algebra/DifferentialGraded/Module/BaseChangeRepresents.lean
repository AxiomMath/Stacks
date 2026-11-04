module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPKFlat

/-! # Base change of a K-flat differential graded module computes the derived base change

Let `R → R'` be a ring map, let `(A, d)` be a differential graded `R`-algebra which is K-flat as
a complex of `R`-modules, and let `A' = A ⊗_R R'`. For a differential graded `A`-module `M` which
is K-flat as a complex of `R`-modules, the ordinary base change `M ⊗_A A'` computes the derived
base change `M ⊗_A^𝐋 A'`: the comparison map from `M ⊗_A^𝐋 A'` to `M ⊗_A A'` is an isomorphism.
No flatness of `R'` over `R` is assumed.

## Main results

* `CochainComplex.DerivedTensor.quasiIso_trightCochain_map_of_kFlat`: a quasi-isomorphism
  between K-flat complexes remains one after tensoring on the right with any complex.
* `DifferentialGraded.quasiIso_absRightTensorMap_of_kFlat`: tensoring with `C` over `R` carries a
  quasi-isomorphism between K-flat complexes to a quasi-isomorphism.
* `DifferentialGraded.quasiIso_tensorCompFunctor_baseChangeBimodule_map_of_kFlat`: tensoring with
  the bimodule `{}_B(B ⊗_R C)_C` carries a quasi-isomorphism between K-flat complexes to a
  quasi-isomorphism.
* `DifferentialGraded.Bimodule.quasiIso_tensorCompFunctor_baseChange_map_of_kFlat`: the same for
  the base change bimodule over `A' = A ⊗_R R'`.
* `DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat`: for `A` and `M`
  K-flat over `R`, the comparison from the derived base change of `M` to `M ⊗_A A'` is an
  isomorphism.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ)
* [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2)
* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.DerivedTensor

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism after tensoring on
the right with any complex `K` and taking the total complex. -/
theorem quasiIso_trightCochain_map_of_kFlat {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (g : X ⟶ Y) (hg : QuasiIso g)
    (hX : CochainComplex.KFlat.{u, u} X) (hY : CochainComplex.KFlat.{u, u} Y) :
    QuasiIso ((TrightCochain K).map g) := by
  have : QuasiIso ((TleftCochain K).map g) := quasiIso_tleftCochain_map.{u, u} g hX hY K
  exact quasiIso_of_arrow_mk_iso ((TleftCochain K).map g) ((TrightCochain K).map g)
    (Arrow.isoMk (tensorFlipIso.{u, u} K X) (tensorFlipIso.{u, u} K Y)
      (tensorFlipIso_naturality.{u, u} K g).symm)

end CochainComplex.DerivedTensor

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-- Tensoring with `C` over `R` carries a quasi-isomorphism `f : P ⟶ M` of differential graded
`B`-modules whose underlying complexes are K-flat to a quasi-isomorphism. No K-flatness is asked
of `C`. -/
theorem quasiIso_absRightTensorMap_of_kFlat
    {P M : DifferentialGradedModule.{u, u, u} B} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex B).map f))
    (hP : CochainComplex.KFlat.{u, u} P.toCochainComplex)
    (hM : CochainComplex.KFlat.{u, u} M.toCochainComplex) :
    QuasiIso (absRightTensorMap B C f) :=
  CochainComplex.DerivedTensor.quasiIso_trightCochain_map_of_kFlat
    (regularModule C).toCochainComplex ((forgetToCochainComplex B).map f) hf hP hM

/-- Tensoring with the bimodule `{}_B(B ⊗_R C)_C` carries a quasi-isomorphism `f : P ⟶ M` of
differential graded `B`-modules whose underlying complexes are K-flat to a quasi-isomorphism. -/
theorem quasiIso_tensorCompFunctor_baseChangeBimodule_map_of_kFlat
    {P M : DifferentialGradedModule.{u, u, u} B} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex B).map f))
    (hP : CochainComplex.KFlat.{u, u} P.toCochainComplex)
    (hM : CochainComplex.KFlat.{u, u} M.toCochainComplex) :
    QuasiIso ((forgetToCochainComplex C).map
      ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f)) := by
  have := quasiIso_absRightTensorMap_of_kFlat B C f hf hP hM
  have h1 : QuasiIso ((absBalancedComplexIso B C P).hom ≫ (forgetToCochainComplex C).map
      ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f)) := by
    rw [← absBalancedComplexIso_naturality B C f]
    exact (quasiIso_iff_comp_right (absRightTensorMap B C f)
      (absBalancedComplexIso B C M).hom).2 inferInstance
  exact (quasiIso_iff_comp_left (absBalancedComplexIso B C P).hom _).1 h1

/-- If `F ≅ G` and `F.map f` is a quasi-isomorphism on underlying complexes, then so is
`G.map f`. -/
theorem quasiIso_forget_map_of_natIso {A' C' : DifferentialGradedAlgebra.{u, u} R}
    {F G : DifferentialGradedModule.{u, u, u} A' ⥤ DifferentialGradedModule.{u, u, u} C'}
    (α : F ≅ G) {P M : DifferentialGradedModule.{u, u, u} A'} (f : P ⟶ M)
    (h : QuasiIso ((forgetToCochainComplex C').map (F.map f))) :
    QuasiIso ((forgetToCochainComplex C').map (G.map f)) := by
  rw [← quasiIso_iff_comp_left ((forgetToCochainComplex C').map (α.hom.app P)),
    ← Functor.map_comp, ← α.hom.naturality f, Functor.map_comp]
  infer_instance

end DifferentialGraded

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Tensoring with the base change bimodule over `A' = A ⊗_R R'` carries a quasi-isomorphism
`f : P ⟶ M` of differential graded `A`-modules whose underlying complexes are K-flat to a
quasi-isomorphism. -/
theorem quasiIso_tensorCompFunctor_baseChange_map_of_kFlat
    {P M : DifferentialGradedModule.{u, u, u} A} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex A).map f))
    (hP : CochainComplex.KFlat.{u, u} P.toCochainComplex)
    (hM : CochainComplex.KFlat.{u, u} M.toCochainComplex) :
    QuasiIso ((forgetToCochainComplex (A.baseChange R')).map
      ((tensorCompFunctor (baseChange A R')).map f)) :=
  quasiIso_forget_map_of_natIso (baseChangeTensorNatIso A R').symm f
    (quasiIso_tensorCompFunctor_baseChangeBimodule_map_of_kFlat A (degreeZero R R') f hf hP hM)

/-- Let `R → R'` be a ring map, `(A, d)` a differential graded `R`-algebra which is K-flat as a
complex of `R`-modules, and `A' = A ⊗_R R'`. For a differential graded `A`-module `M` which is
K-flat as a complex of `R`-modules, the comparison from the derived base change `M ⊗_A^𝐋 A'` to
the ordinary base change `M ⊗_A A'` is an isomorphism at `M`, so `M ⊗_A A'` represents
`M ⊗_A^𝐋 A'`. Nothing is asked of `R'`. -/
@[stacks 0BYZ "part (3): M K-flat as a complex of R-modules implies that the ordinary base \
change represents M (x)_A^L A'. The representing object is spelled M (x)_A A'; it is the \
source's differential graded A'-module M (x)_R R' by baseChangeTensorIso over R' and by \
baseChangeTensorAlgebraIso of BaseChangeAbsoluteTensor.lean over A'. Part (2) is \
derivedBaseChangeRestrictionSquare of BaseChangeRestrictionSquare.lean"]
theorem isIso_derivedBaseChangeCounit_app_of_kFlat
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex)
    (M : DifferentialGradedModule.{u, u, u} A)
    (hM : CochainComplex.KFlat.{u, u} M.toCochainComplex) :
    IsIso ((derivedBaseChangeCounit A R').app ((toHomotopyCategory A).obj M)) := by
  obtain ⟨P, f, hf, hFP⟩ := DifferentialGradedModule.exists_propertyP_resolution A M
  exact (isIso_derivedTensorFunctorCounit_app_iff_quasiIso_of_propertyP
    (baseChange A R') f hf hFP).2
    (quasiIso_tensorCompFunctor_baseChange_map_of_kFlat A R' f hf
      (DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration hA hFP.some) hM)

end DifferentialGraded.Bimodule

end
