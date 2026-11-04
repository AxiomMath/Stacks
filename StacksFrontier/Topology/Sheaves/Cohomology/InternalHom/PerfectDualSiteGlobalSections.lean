module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect

/-!
# The dual of a perfect object computes morphisms out of it, at a ringed site

Let `X` be a ringed site, `L` a perfect object of `D(O)` and `N` any object. The canonical map
of Stacks 08JD on degree-zero global hypercohomology

`H⁰(C, N ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, N)`

is bijective (Stacks 08JJ, the form of Stacks 08DQ at a ringed site). Combined with
`H⁰(C, Z) ≃+ Hom_{D(O)}(O, Z)` it gives an additive bijection, natural in `N`,

`Hom_{D(O)}(L, N) ≃+ Hom_{D(O)}(O, N ⊗^L_O L^∨)`.

## Main results

* `AlgebraicGeometry.RingedSite.bijective_derivedTensorDualGlobalSectionsMap_of_isIso`: the map
  is bijective when the canonical morphism `N ⊗^L_O L^∨ ⟶ RSheafHom(L, N)` is invertible.
* `AlgebraicGeometry.RingedSite.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect`: the
  map is bijective for a perfect `L`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsAddEquiv`: that bijection as an
  additive equivalence.
* `AlgebraicGeometry.RingedSite.derivedDualHomFromStructureSheafEquiv`: the resulting additive
  bijection `Hom(L, N) ≃+ Hom(O, N ⊗^L L^∨)`.
* `AlgebraicGeometry.RingedSite.derivedDualHomFromStructureSheafEquiv_naturality`: it carries
  postcomposition on the left to `T` applied on the right.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Lemma 20.50.9 (Tag 09JC)](https://stacks.math.columbia.edu/tag/09JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The map of Stacks 08JD is bijective whenever the canonical morphism is invertible.**  If
the canonical morphism `N ⊗^L_O L^∨ ⟶ RSheafHom(L, N)` is an isomorphism, then the map
`H⁰(C, N ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, N)` on degree-zero global hypercohomology is bijective. -/
theorem bijective_derivedTensorDualGlobalSectionsMap_of_isIso
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsIso (derivedTensorDualToSheafHom X T L N)) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap X T L N) :=
  (derivedSheafHomGlobalSectionsEquiv X L N).bijective.comp
    (ConcreteCategory.bijective_of_isIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedTensorDualToSheafHom X T L N))))

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- For a perfect object `L` of `D(O)` and any object `N` the map of Stacks 08JD

`H⁰(C, N ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, N)`

is bijective. -/
theorem bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap X T L N) :=
  bijective_derivedTensorDualGlobalSectionsMap_of_isIso X T L N
    (isIso_derivedTensorDualToSheafHom_of_isPerfect X T L N hL)

/-- For a perfect `L`, the map of Stacks 08JD as an isomorphism of abelian groups
`H⁰(C, N ⊗^L_O L^∨) ≃+ Hom_{D(O)}(L, N)`. -/
def derivedTensorDualGlobalSectionsAddEquiv
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          ((T.tensor.obj N).obj (derivedDual X L))) : Type u) ≃+ (L ⟶ N) :=
  AddEquiv.ofBijective (derivedTensorDualGlobalSectionsMap X T L N)
    (bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect X T L N hL)

/-- **Morphisms out of a perfect object are morphisms out of the structure sheaf into the
twist by its dual.**  For a perfect `L`, the additive bijection

`Hom_{D(O)}(L, N) ≃+ Hom_{D(O)}(O, N ⊗^L_O L^∨)`

given by the inverse of `derivedTensorDualGlobalSectionsAddEquiv` followed by the identification
`H⁰(C, Z) ≃+ Hom(O, Z)` of `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`.
-/
def derivedDualHomFromStructureSheafEquiv
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L) :
    (L ⟶ N) ≃+ (derivedStructureSheaf X ⟶ (T.tensor.obj N).obj (derivedDual X L)) :=
  (derivedTensorDualGlobalSectionsAddEquiv X T L N hL).symm.trans
    (derivedStructureSheafGlobalSectionsEquiv X ((T.tensor.obj N).obj (derivedDual X L)))

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The equivalence is compatible with composition.**  For `f : L ⟶ N` and `g : N ⟶ N'` the
bijection carries `f ≫ g` to the image of `f` followed by `N ⊗^L L^∨ ⟶ N' ⊗^L L^∨`. -/
theorem derivedDualHomFromStructureSheafEquiv_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L)
    {N N' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : L ⟶ N) (g : N ⟶ N') :
    derivedDualHomFromStructureSheafEquiv X T L N' hL (f ≫ g) =
      derivedDualHomFromStructureSheafEquiv X T L N hL f ≫
        (T.tensor.map g).app (derivedDual X L) := by
  set z := (derivedTensorDualGlobalSectionsAddEquiv X T L N hL).symm f with hz
  have hfz : derivedTensorDualGlobalSectionsMap X T L N z = f :=
    (derivedTensorDualGlobalSectionsAddEquiv X T L N hL).apply_symm_apply f
  have hstep : derivedTensorDualGlobalSectionsMap X T L N'
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map ((T.tensor.map g).app (derivedDual X L))) z) =
      f ≫ g := by
    rw [derivedTensorDualGlobalSectionsMap_naturality X T L g z, hfz]
  have hz' : (derivedTensorDualGlobalSectionsAddEquiv X T L N' hL).symm (f ≫ g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map ((T.tensor.map g).app (derivedDual X L))) z := by
    rw [← hstep]
    exact (derivedTensorDualGlobalSectionsAddEquiv X T L N' hL).symm_apply_apply _
  rw [derivedDualHomFromStructureSheafEquiv, derivedDualHomFromStructureSheafEquiv,
    AddEquiv.trans_apply, AddEquiv.trans_apply, hz', ← hz]
  exact derivedStructureSheafGlobalSectionsEquiv_naturality X
    ((T.tensor.map g).app (derivedDual X L)) z

end AlgebraicGeometry.RingedSite

end
