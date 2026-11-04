module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionTensorComparison
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeIdentification

/-!
# The tensor-comparison obligation has only to be checked at a K-flat complex

`Dualizing.TensorComparisonCompatibility` is the identity at an object `X` of `D(R)` to which
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionTensorComparison` reduces the
projection-formula compatibility of [stacks 0E2A]. Both of its sides are natural in `X`, so it
transfers along isomorphisms of `D(R)`, and it holds at every object once it holds at the
localizations of K-flat complexes of `R`-modules.

## Main results

* `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_naturality`: the comparison of the two
  endofunctors across a square of adjunctions is natural.
* `Dualizing.tensorComparisonCompatibility_of_iso`: the obligation transfers along an
  isomorphism of `D(R)`.
* `Dualizing.tensorComparisonCompatibility_of_kFlat`: it is enough to check the obligation at the
  localizations of K-flat complexes of `R`-modules.

A second, independent reduction of the same variable is
`Dualizing.tensorComparisonCompatibility_of_restrict_extend`: the obligation at `X` follows from
the obligation at `(Ff X)|_R`, so it is enough to check it at the objects restricted from `D(A)`.
That one is not a transfer along an isomorphism — the comparison `Lg` of the unit is only split
monic — and the two compose, by
`Dualizing.tensorComparisonCompatibility_of_kFlat_restrict_extend`.

## Implementation notes

No `@[stacks]` attribute is placed here: the obligation itself is still open, so nothing in this
file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The comparison of the two endofunctors across the square is natural.** For any four
isomorphisms `pf`, `pf'`, `γ`, `Θ` (no mate condition is assumed),
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso pf pf' γ Θ` is natural in the object it
is read at. -/
theorem tensorComparisonOfIso_naturality {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) {X Y : A} (h : X ⟶ Y) :
    Lg.map (Tens.map h) ≫ tensorComparisonOfIso pf pf' γ Θ Y =
      tensorComparisonOfIso pf pf' γ Θ X ≫ Tens'.map (Lg.map h) := by
  have h1 := pf.inv.naturality h
  have h2 := Θ.inv.naturality (Lf.map h)
  have h3 := γ.hom.naturality h
  have h4 := pf'.hom.naturality (Lg.map h)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3 h4
  have h34 : Rf'.map (Lg'.map (Lf.map h)) ≫ Rf'.map (γ.hom.app Y) ≫ pf'.hom.app (Lg.obj Y) =
      Rf'.map (γ.hom.app X) ≫ pf'.hom.app (Lg.obj X) ≫ Tens'.map (Lg.map h) := by
    rw [← Category.assoc, ← Rf'.map_comp, h3, Rf'.map_comp, Category.assoc, h4]
  dsimp only [tensorComparisonOfIso]
  simp only [Category.assoc]
  rw [← Category.assoc (Lg.map (Tens.map h)), ← Lg.map_comp, h1, Lg.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h2, h34]

end Stacks.CategoryTheory.BaseChange

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The tensor-comparison obligation transfers along an isomorphism.** If
`Dualizing.TensorComparisonCompatibility` holds at `X` and `X ≅ Y` in `D(R)`, it holds at `Y`. -/
theorem tensorComparisonCompatibility_of_iso
    {X Y : DerivedCategory (ModuleCat.{max v uR uA uRp} R)} (e : X ≅ Y)
    (h : TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai Y := by
  replace h : _ = _ := h
  show _ = _
  have hmu := derivedTensorBaseChange_naturality.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR e.hom
    (𝟙 (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
  rw [baseChangeR.map_id] at hmu
  have hcomp := Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_naturality
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA) e.hom
  rw [derivedExtendRestrictScalarsTensorFunctor_map,
    derivedExtendRestrictScalarsTensorFunctor_map] at hcomp
  refine (Iso.cancel_iso_hom_left
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
        max v uR uA uRp + 1} R').tensor.mapIso
      ((baseChangeR.mapIso e).prod (Iso.refl (baseChangeR.obj
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))))) _ _).mp ?_
  have hpair : ((baseChangeR.mapIso e).prod (Iso.refl (baseChangeR.obj
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))))).hom =
      (baseChangeR.map e.hom,
        𝟙 (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) := rfl
  dsimp only [CategoryTheory.Functor.mapIso_hom]
  rw [hpair]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) hmu) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) hcomp) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) h) ?_
  refine Eq.trans ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').tensor_map_comp _ _ _ _) (Eq.trans ?_
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').tensor_map_comp _ _ _ _).symm)
  exact congrArg _ (Prod.ext
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm))

include hf hA hR hi in
/-- **The obligation has only to be checked at K-flat complexes.** If
`Dualizing.TensorComparisonCompatibility` holds at the localization of every K-flat complex of
`R`-modules, it holds at every object of `D(R)`, each of which is isomorphic to such a
localization ([stacks 06Y4]). -/
theorem tensorComparisonCompatibility_of_kFlat
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai (DerivedCategory.Q.obj K))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_kFlat_iso.{uR, max v uA uRp} X
  exact tensorComparisonCompatibility_of_iso hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai e.symm (h K hK)

end Dualizing

end
