module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafTensor

/-!
# The derived tensor product with a complex of torsion modules has torsion cohomology

Let `O` be a sheaf of commutative rings on a small site and `P` a complex of sheaves of
`O`-modules all of whose terms are torsion (`Stacks.Torsion.torsionModules`). Then for every
object `L` of `D(O)` all cohomology sheaves of `P ⊗^L_O L` are torsion.

A K-flat resolution `L'` of `L` computes the derived tensor product with any left complex
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonRight`), so `P ⊗^L_O L` is the
total tensor complex of `P` and `L'`. Its term in degree `n` receives the jointly epimorphic
family of inclusions of the summands `P^p ⊗_O L'^q`, `p + q = n`, each of which is torsion
(`Stacks.Torsion.torsionModules_sheafTensor_obj_obj`), so it is torsion
(`Stacks.Torsion.torsionModules_of_jointlyEpi`), and cohomology, a quotient of a subobject,
stays in the Serre class.

## Main results

* `Stacks.Torsion.torsionModules_homology_tensor`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Torsion

universe d u

open Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- **A complex with torsion terms has torsion cohomology.** -/
theorem torsionModules_homology_of_torsion_terms (K : CochainComplex (Modules R) ℤ)
    (hK : ∀ p, torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R) (K.X p)) (n : ℤ) :
    torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R) (K.homology n) :=
  (torsionModules _).prop_of_epi (K.homologyπ n)
    ((torsionModules _).prop_of_mono (K.iCycles n) (hK n))

omit [HasDerivedCategory.{d} (Modules R)] in
/-- **The total tensor complex of a complex with torsion terms and any complex has torsion
terms**: its term in degree `n` receives the jointly epimorphic family of the summands
`P^p ⊗_O L^q`, `p + q = n`, each torsion. -/
theorem torsionModules_mapBifunctor_X (P L : CochainComplex (Modules R) ℤ)
    (hP : ∀ p, torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R) (P.X p)) (n : ℤ) :
    torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R)
      ((HomologicalComplex.mapBifunctor P L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)).X n) :=
  torsionModules_of_jointlyEpi
    (fun (x : {pq : ℤ × ℤ //
        ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n}) =>
      HomologicalComplex.ιMapBifunctor P L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ) x.1.1 x.1.2 n x.2)
    (fun _ => torsionModules_sheafTensor_obj_obj R _ _ (hP _))
    (fun _ _ _ h => HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => h ⟨(p, q), hpq⟩)

/-- **The derived tensor product of a complex with torsion terms with any object has torsion
cohomology.** -/
theorem torsionModules_homology_tensor (T : DerivedTensorProduct R)
    (P : CochainComplex (Modules R) ℤ)
    (hP : ∀ p, torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R) (P.X p))
    (B : DerivedModules R) (n : ℤ) :
    torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((T.tensor.obj (DerivedCategory.Q.obj P)).obj B)) := by
  obtain ⟨L, f, hL, hf⟩ := exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage B)
  let e : (T.tensor.obj (DerivedCategory.Q.obj P)).obj B ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P L
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) :=
    (T.tensor.obj (DerivedCategory.Q.obj P)).mapIso
        ((DerivedCategory.Q.objObjPreimageIso B).symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm) ≪≫
      T.comparisonRight P L hL
  refine (torsionModules _).prop_of_iso
    (((DerivedCategory.homologyFunctor _ n).mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _).symm ?_
  exact torsionModules_homology_of_torsion_terms R _ (torsionModules_mapBifunctor_X R P L hP) n

end Stacks.Torsion
