module

public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceTransport
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.PerfectDualTensor
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# `H^i(K ⊗ᴸ_A M)` as morphisms out of a perfect object, with the boundary maps

Let `A` be a ring and `X` a perfect object of `D(A)`. Perfect duality ([Stacks, Tag 07VI])
produces a perfect object `K` of `D(A)`, the derived dual of `X`, with

`Hⁱ(K ⊗ᴸ_A M) ≅ Hom_{D(A)}(X, M[i])`

for every `A`-module `M` and every `i`, naturally in `M`, and such that the connecting map
`H¹(K ⊗ᴸ_A M₃) ⟶ H²(K ⊗ᴸ_A M₁)` of a short exact sequence `0 → M₁ → M₂ → M₃ → 0`
(`Deformation.Artin.boundaryMap`) is composition with the boundary morphism
`M₃ ⟶ M₁[1]` of the sequence, shifted by one. The left-hand side is
`Deformation.Artin.derivedCohomology A K i`, the cohomology of the derived tensor product
`CochainComplex.DerivedTensor.derivedTensorProduct K`.

## Main results

* `Deformation.Artin.exists_isPerfect_homologyZero_derivedTensorProduct_addEquiv`: degree zero,
  `H⁰(K ⊗ᴸ_A L) ≃+ Hom_{D(A)}(X, L)` naturally in `L ∈ D(A)`.
* `Deformation.Artin.exists_isPerfect_derivedCohomology_addEquiv_shiftedHom`: every degree,
  naturally in the module, with the boundary maps.

## Implementation notes

Degree zero is [Stacks, Tag 07VI] over the lifted ring `ULift A`
(`StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos`), read over `A` through the scalar
transport `Deformation.Artin.scalarEquiv` and then for
`CochainComplex.DerivedTensor.derivedTensorProduct` through
`Deformation.Artin.nonempty_derivedTensorProduct_iso_tensorOverRing'`.

The other degrees and the boundary maps come from
`Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso`: for the homological functor `H⁰` and
the functor `K ⊗ᴸ_A -`, which commutes with the shifts, an identification of `H⁰(K ⊗ᴸ_A -)` with
`Hom(X, -)` determines identifications in every degree, and these carry the connecting
morphism of the image of a triangle to composition with its shifted third morphism. That
argument uses nothing about the shift-compatibility of `K ⊗ᴸ_A -` beyond its existence, which
is what makes it applicable to `CochainComplex.DerivedTensor.derivedTensorProduct`, whose
commutation with the shifts is a chosen one.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedTensor StacksDraft.DerivedHom

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Degree-zero perfect duality for `CochainComplex.DerivedTensor.derivedTensorProduct`.**
For a perfect object `X` of `D(A)` there is a perfect object `K` (the derived dual of `X`) with
additive isomorphisms `H⁰(K ⊗ᴸ_A L) ≃+ Hom_{D(A)}(X, L)`, natural in `L ∈ D(A)`. -/
theorem exists_isPerfect_homologyZero_derivedTensorProduct_addEquiv
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : StacksDraft.Perfect.IsPerfect X) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect K)
      (e : ∀ L : DerivedCategory (ModuleCat.{u} A),
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedTensorProduct K).obj L) : Type u) ≃+ (X ⟶ L)),
      ∀ {L L' : DerivedCategory (ModuleCat.{u} A)} (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedTensorProduct K).obj L)),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedTensorProduct K).map f) a) = e L a ≫ f := by
  set E := scalarEquiv A with hE
  set d' := liftedData A with hd'
  set H0A := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH0A
  set H0U := DerivedCategory.homologyFunctor (ModuleCat.{u} (ULift.{0} A)) 0 with hH0U
  have hX₀ : StacksDraft.Perfect.IsPerfect (E.inverse.obj X) :=
    StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv
      (ULift.ringEquiv.{u, 0} (R := A)).symm.symm X hX
  set W := StacksDraft.Perfect.derivedDual (E.inverse.obj X) with hW
  have hdual := StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos (E.inverse.obj X) hX₀
  obtain ⟨e, he⟩ := hdual.exists_extZeroEquiv
  have hK : StacksDraft.Perfect.IsPerfect (E.functor.obj W) :=
    StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv
      (ULift.ringEquiv.{u, 0} (R := A)).symm W hdual.dual_isPerfect
  obtain ⟨β⟩ := nonempty_derivedTensorProduct_iso_tensorOverRing' (E.functor.obj W)
  let τ : ∀ L : DerivedCategory (ModuleCat.{u} A),
      (overRingData A).tensor.obj (L, E.functor.obj W) ≅
        E.functor.obj (d'.tensor.obj (E.inverse.obj L, W)) := fun L =>
    (overRingData A).tensor.mapIso ((E.counitIso.app L).symm.prod (Iso.refl _)) ≪≫
      (derivedTensorULiftIso.{u, 0, u + 1} A).app (E.inverse.obj L, W)
  have hτ : ∀ {L L' : DerivedCategory (ModuleCat.{u} A)} (f : L ⟶ L'),
      (overRingData A).tensor.map (f, 𝟙 (E.functor.obj W)) ≫ (τ L').hom =
        (τ L).hom ≫ E.functor.map (d'.tensor.map ((E.inverse.map f, 𝟙 W) :
          ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W))) := by
    intro L L' f
    have hprod :
        ((f, 𝟙 (E.functor.obj W)) : ((L, E.functor.obj W) : DerivedCategory (ModuleCat.{u} A) ×
            DerivedCategory (ModuleCat.{u} A)) ⟶ (L', E.functor.obj W)) ≫
          ((E.counitIso.app L').symm.prod (Iso.refl (E.functor.obj W))).hom =
        ((E.counitIso.app L).symm.prod (Iso.refl (E.functor.obj W))).hom ≫
          ((E.functor.map (E.inverse.map f), E.functor.map (𝟙 W)) :
            ((E.functor.obj (E.inverse.obj L), E.functor.obj W) :
                DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (E.functor.obj (E.inverse.obj L'), E.functor.obj W)) := by
      refine Prod.ext ?_ ?_
      · exact E.counitIso.inv.naturality f
      · simp
    have hnat :
        (overRingData A).tensor.map
            ((E.functor.map (E.inverse.map f), E.functor.map (𝟙 W)) :
              ((E.functor.obj (E.inverse.obj L), E.functor.obj W) :
                  DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
                (E.functor.obj (E.inverse.obj L'), E.functor.obj W)) ≫
          ((derivedTensorULiftIso.{u, 0, u + 1} A).app (E.inverse.obj L', W)).hom =
        ((derivedTensorULiftIso.{u, 0, u + 1} A).app (E.inverse.obj L, W)).hom ≫
          E.functor.map (d'.tensor.map ((E.inverse.map f, 𝟙 W) :
            ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
              DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W))) :=
      (derivedTensorULiftIso.{u, 0, u + 1} A).hom.naturality
        ((E.inverse.map f, 𝟙 W) :
          ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W))
    dsimp only [τ, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, hprod, Functor.map_comp, Category.assoc, hnat,
      Category.assoc]
  refine ⟨E.functor.obj W, hK, fun L =>
    ((H0A.mapIso (β.app L ≪≫ τ L)).toLinearEquiv.toAddEquiv).trans
      ((scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0).trans
        ((e (E.inverse.obj L)).trans
          ((equivalenceHomAddEquiv E (E.inverse.obj X) (E.inverse.obj L)).trans
            (Stacks.Injectives.homCongrAddEquiv (E.counitIso.app X) (E.counitIso.app L))))), ?_⟩
  intro L L' f a
  have hβ : (derivedTensorProduct (E.functor.obj W)).map f ≫ (β.app L').hom =
      (β.app L).hom ≫ (overRingData A).tensor.map (f, 𝟙 (E.functor.obj W)) :=
    β.hom.naturality f
  have key : scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        ((H0A.mapIso (β.app L' ≪≫ τ L')).toLinearEquiv.toAddEquiv
          (H0A.map ((derivedTensorProduct (E.functor.obj W)).map f) a)) =
      H0U.map (d'.tensor.map ((E.inverse.map f, 𝟙 W) :
          ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W)))
        (scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0
          ((H0A.mapIso (β.app L ≪≫ τ L)).toLinearEquiv.toAddEquiv a)) := by
    simp only [LinearEquiv.coe_toAddEquiv]
    show scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        (H0A.map ((β.app L').hom ≫ (τ L').hom)
          (H0A.map ((derivedTensorProduct (E.functor.obj W)).map f) a)) = _
    rw [← Functor.map_comp_apply, ← Category.assoc, hβ, Category.assoc, hτ, ← Category.assoc,
      Functor.map_comp_apply]
    exact scalarHomologyAddEquiv_naturality.{u, 0} A _ 0 _
  have hcounit : E.functor.map (E.inverse.map f) ≫ (E.counitIso.app L').hom =
      (E.counitIso.app L).hom ≫ f := E.counitIso.hom.naturality f
  simp only [AddEquiv.trans_apply]
  rw [key, he (E.inverse.map f), equivalenceHomAddEquiv_comp,
    Stacks.Injectives.homCongrAddEquiv_apply, Stacks.Injectives.homCongrAddEquiv_apply]
  simp only [Category.assoc]
  rw [hcounit]

/-- `H⁰(K ⊗ᴸ_A -) ≅ Hom_{D(A)}(X, -)` as an isomorphism of functors `D(A) ⥤ Ab`, universe-lifted,
from additive isomorphisms natural in the argument. -/
private def homologyZeroIsoCoyoneda {K X : DerivedCategory (ModuleCat.{u} A)}
    (e : ∀ L : DerivedCategory (ModuleCat.{u} A),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((derivedTensorProduct K).obj L) : Type u) ≃+ (X ⟶ L))
    (he : ∀ {L L' : DerivedCategory (ModuleCat.{u} A)} (f : L ⟶ L')
      (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((derivedTensorProduct K).obj L)),
      e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((derivedTensorProduct K).map f) a) = e L a ≫ f) :
    derivedTensorProduct K ⋙ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (0 : ℤ) ⋙
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≅
      preadditiveCoyoneda.obj (Opposite.op X) :=
  NatIso.ofComponents (fun L => (AddEquiv.ulift.trans (e L)).toAddCommGrpIso) (by
    intro L L' f
    ext ⟨y⟩
    exact he f y)

/-- **`Hⁱ(K ⊗ᴸ_A M) ≃+ Hom_{D(A)}(X, M[i])` for a perfect `X`, with the boundary maps.** For a
perfect object `X` of `D(A)` there is a perfect object `K` (the derived dual of `X`) and additive
isomorphisms `Hⁱ(K ⊗ᴸ_A M) ≃+ Hom_{D(A)}(X, M[0][i])` for every `A`-module `M` and every `i`,
natural in `M`, which carry the connecting map `H¹(K ⊗ᴸ_A M₃) ⟶ H²(K ⊗ᴸ_A M₁)` of a short exact
sequence `0 → M₁ → M₂ → M₃ → 0` to composition with its boundary morphism
`M₃[0] ⟶ M₁[0][1]`, shifted by one. -/
theorem exists_isPerfect_derivedCohomology_addEquiv_shiftedHom
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : StacksDraft.Perfect.IsPerfect X) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect K)
      (e : ∀ (M : ModuleCat.{u} A) (i : ℤ),
        ((derivedCohomology A K i).obj M : Type u) ≃+
          (X ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦i⟧)),
      (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (y : (derivedCohomology A K i).obj M),
        e N i ((derivedCohomology A K i).map g y) =
          e M i y ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)⟦i⟧') ∧
      (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
        (y : (derivedCohomology A K 1).obj Sq.X₃),
        e Sq.X₁ 2 (boundaryMap A K hSq y) =
          e Sq.X₃ 1 y ≫ hSq.singleδ⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) 1 1 2 (by norm_num)).inv.app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) := by
  obtain ⟨K, hK, e₀, he₀⟩ := exists_isPerfect_homologyZero_derivedTensorProduct_addEquiv A X hX
  let Φ := Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso (derivedTensorProduct K)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
    (preadditiveCoyoneda.obj (Opposite.op X)) (homologyZeroIsoCoyoneda A e₀ he₀)
  refine ⟨K, hK, fun M i => AddEquiv.ulift.symm.trans
    ((Φ i).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).addCommGroupIsoToAddEquiv,
    ?_, ?_⟩
  · intro M N g i y
    have h := ConcreteCategory.congr_hom
      ((Φ i).hom.naturality ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)) ⟨y⟩
    have key : ((Φ i).hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
          ⟨(derivedCohomology A K i).map g y⟩ =
        ((Φ i).hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⟨y⟩ ≫
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)⟦i⟧' := h
    exact key
  · intro Sq hSq y
    have h := ConcreteCategory.congr_hom
      (Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso_delta (derivedTensorProduct K)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
        (preadditiveCoyoneda.obj (Opposite.op X)) (homologyZeroIsoCoyoneda A e₀ he₀)
        hSq.singleδ 1 2 (by norm_num)) ⟨y⟩
    have key : ((Φ 2).hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁))
          ⟨boundaryMap A K hSq y⟩ =
        ((Φ 1).hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₃)) ⟨y⟩ ≫
          hSq.singleδ⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) 1 1 2 (by norm_num)).inv.app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁) := h
    exact key

end Deformation.Artin

end
