module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateUnit

/-!
# Derived base change is strongly monoidal: the lax structure map is invertible

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map
`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` of a model `F` of derived extension of scalars along
`f : R → A`, built as a double adjoint transpose through the derived-Hom base-change morphism of
[stacks 0E1X]. This file proves that `μ` is an isomorphism.

The change-of-rings isomorphism `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso` of
[stacks 0E1W] identifies `RHom_R(Y, (-)|_R)` with `RHom_A(F Y, -)|_R`, so for every object `Z` of
`D(A)` the four bijections

`Hom_A(F X ⊗ᴸ_A F Y, Z) ≅ Hom_A(F X, RHom_A(F Y, Z)) ≅ Hom_R(X, RHom_A(F Y, Z)|_R)`

`≅ Hom_R(X, RHom_R(Y, Z|_R)) ≅ Hom_R(X ⊗ᴸ_R Y, Z|_R) ≅ Hom_A(F (X ⊗ᴸ_R Y), Z)`

— the tensor–Hom adjunction of [stacks 0A63] over `A`, the extension-of-scalars adjunction of
[stacks 0GMT], the inverse of [stacks 0E1W], [stacks 0A63] over `R`, and [stacks 0GMT] again —
compose to a bijection `Hom_A(F X ⊗ᴸ_A F Y, Z) ≅ Hom_A(F (X ⊗ᴸ_R Y), Z)`. Taking `Z` to be
`F X ⊗ᴸ_A F Y` and the identity produces `ν_{X,Y} : F (X ⊗ᴸ_R Y) ⟶ F X ⊗ᴸ_A F Y`, and that
bijection is precomposition with `ν`. Hence precomposition with `ν` is injective, `ν ≫ μ = 𝟙`,
and `μ ≫ ν = 𝟙`.

## Main definitions

* `Dualizing.derivedTensorBaseChangeSection`: the morphism `ν_{X,Y} : F (X ⊗ᴸ_R Y) ⟶ F X ⊗ᴸ_A F Y`
  transposing to the identity under the four bijections above.

## Main results

* `Dualizing.homEquiv_derivedTensorBaseChangeSection_tensorHomUnit` and
  `Dualizing.homEquiv_derivedTensorBaseChangeSection`: the composite of the four bijections is
  precomposition with `ν`.
* `Dualizing.derivedTensorBaseChangeSection_comp_injective`: precomposition with `ν` is injective.
* `Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange`: `ν ≫ μ = 𝟙`.
* `Dualizing.derivedTensorBaseChange_comp_derivedTensorBaseChangeSection`: `μ ≫ ν = 𝟙`.
* `Dualizing.isIso_derivedTensorBaseChange`: the lax monoidal structure map of derived base
  change is an isomorphism, with inverse `ν`.

## Implementation notes

Most steps are written with `Eq.trans` and `congrArg` rather than `rw`. The pair-morphism
arguments of the tensor and internal-Hom bifunctors are elaborated at the product category's
`Quiver.Hom`, against which keyed matching does not fire, and the source of a component of
[stacks 0E1W] is spelled as the value of a composite functor, which is only definitionally the
restriction of an internal Hom.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- The naturality of the inverse of the change-of-rings isomorphism of [stacks 0E1W] in its
covariant variable, at a morphism `(𝟙, ψ)` of `D(R)ᵒᵖ × D(A)`, stated for the internal Homs of
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`. -/
private theorem restrictScalars_map_hom_map_comp_derivedHomRestrictScalarsNatIso_inv
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (psi : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
      (F.obj X, F.obj Y) ⟶ Z) :
    (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
            ((𝟙 (Opposite.op (F.obj Y)), psi) :
              (Opposite.op (F.obj Y),
                  (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y)) ⟶
                (Opposite.op (F.obj Y), Z))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app (Opposite.op Y, Z) =
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app
          (Opposite.op Y,
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
              (F.obj X, F.obj Y)) ≫
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.map
          ((𝟙 (Opposite.op Y),
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map psi) :
            (Opposite.op Y,
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y))) ⟶
              (Opposite.op Y,
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)) := by
  have hnat := (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
    comparison).inv.naturality
    ((𝟙 (Opposite.op Y), psi) :
      ((Opposite.op Y,
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
              max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y)) :
          (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ ×
            DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶ (Opposite.op Y, Z))
  simp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map, unop_id,
    CategoryTheory.Functor.map_id, op_id] at hnat
  exact hnat

/-- Composing with the component of [stacks 0E1W] and then with its inverse is the identity. -/
private theorem comp_natIso_inv_comp_natIso_hom
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    {K : DerivedCategory (ModuleCat.{max uR uA uM} R)}
    (k : K ⟶ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
        (Opposite.op (F.obj Y), Z))) :
    (k ≫ (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app (Opposite.op Y, Z)) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).hom.app (Opposite.op Y, Z) = k :=
  by erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Composing with the inverse component of [stacks 0E1W] and then with the component is the
identity. -/
private theorem comp_natIso_hom_comp_natIso_inv
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    {K : DerivedCategory (ModuleCat.{max uR uA uM} R)}
    (k : K ⟶ (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
      (Opposite.op Y, (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)) :
    (k ≫ (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).hom.app (Opposite.op Y, Z)) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app (Opposite.op Y, Z) = k :=
  by erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The morphism `ν_{X,Y} : F (X ⊗ᴸ_R Y) ⟶ F X ⊗ᴸ_A F Y` whose transpose, over the
extension-of-scalars adjunction of [stacks 0GMT] along `f` followed by the tensor–Hom adjunction of
[stacks 0A63] over `R`, is the transposed coevaluation of [stacks 0A63] over `A` read backwards
through the change-of-rings isomorphism of [stacks 0E1W]. -/
noncomputable def derivedTensorBaseChangeSection
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y)) ⟶
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) :=
  ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ _).symm
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
      ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
            (F.obj X) (F.obj Y)) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app
          (Opposite.op Y,
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
              (F.obj X, F.obj Y))))

/-- For `ψ : F X ⊗ᴸ_A F Y ⟶ Z` the transpose over [stacks 0GMT] of the coevaluation of
[stacks 0A63] at `A` followed by the internal Hom of `ψ`, read backwards through [stacks 0E1W] and
transposed over [stacks 0A63] at `R`, is the transpose over [stacks 0GMT] of `ν_{X,Y} ≫ ψ`. -/
theorem homEquiv_derivedTensorBaseChangeSection_tensorHomUnit
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (psi : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
      (F.obj X, F.obj Y) ⟶ Z) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
        ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
                (F.obj X) (F.obj Y) ≫
              (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
                ((𝟙 (Opposite.op (F.obj Y)), psi) :
                  (Opposite.op (F.obj Y),
                      (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                        max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y)) ⟶
                    (Opposite.op (F.obj Y), Z))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app (Opposite.op Y, Z)) =
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ Z
        (derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫ psi) := by
  have inner :
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
                (F.obj X) (F.obj Y) ≫
              (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
                ((𝟙 (Opposite.op (F.obj Y)), psi) :
                  (Opposite.op (F.obj Y),
                      (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                        max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y)) ⟶
                    (Opposite.op (F.obj Y), Z))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app (Opposite.op Y, Z) =
        ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
              ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).tensorHomUnit (F.obj X) (F.obj Y)) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
                comparison).inv.app
              (Opposite.op Y,
                (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y))) ≫
          (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.map
            ((𝟙 (Opposite.op Y),
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map psi) :
              (Opposite.op Y,
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y))) ⟶
                (Opposite.op Y,
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)) := by
    rw [Adjunction.homEquiv_naturality_right]
    exact Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg (fun z => _ ≫ z)
      (restrictScalars_map_hom_map_comp_derivedHomRestrictScalarsNatIso_inv.{uR, uA, uM} f F
        comparison X Y Z psi))
      (Category.assoc _ _ _).symm)
  have hnu : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
        ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
              max uR uA uM + 1} A).tensorHomUnit (F.obj X) (F.obj Y)) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app
            (Opposite.op Y,
              (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y))) =
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ _
        (derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y) :=
    (Equiv.apply_symm_apply _ _).symm
  refine Eq.trans (congrArg (fun z =>
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _ z)
      inner) ?_
  refine Eq.trans ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
    max uR uA uM + 1} R).homEquiv_naturality_right _ _) ?_
  exact Eq.trans (congrArg (fun z => z ≫ _) hnu)
    (Adjunction.homEquiv_naturality_right _ _ _).symm

/-- For `g : F X ⟶ RHom_A(F Y, Z)` the transpose of `g` over [stacks 0GMT], read backwards through
[stacks 0E1W] and transposed over [stacks 0A63] at `R`, is the transpose over [stacks 0GMT] of
`ν_{X,Y}` followed by the transpose of `g` over [stacks 0A63] at `A`. -/
theorem homEquiv_derivedTensorBaseChangeSection
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (g : F.obj X ⟶ (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
      max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj Y), Z)) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
        ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _ g ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app (Opposite.op Y, Z)) =
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ Z
        (derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
            (F.obj X) (F.obj Y) Z g) := by
  have hg := DerivedHomAdjunction.tensorHomUnit_comp_hom_map
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A) (F.obj X) (F.obj Y) Z
    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
      (F.obj X) (F.obj Y) Z g)
  rw [AddEquiv.symm_apply_apply] at hg
  refine Eq.trans (congrArg (fun z =>
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
      ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _ z ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app (Opposite.op Y, Z))) hg.symm) ?_
  exact homEquiv_derivedTensorBaseChangeSection_tensorHomUnit.{uR, uA, uM} f F comparison X Y Z _

/-- Precomposition with `ν_{X,Y}` is injective. -/
theorem derivedTensorBaseChangeSection_comp_injective
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    {h h' : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
      (F.obj X, F.obj Y) ⟶ Z}
    (hyp : derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫ h =
      derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫ h') :
    h = h' := by
  have key : ∀ k : (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
      max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y) ⟶ Z,
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ Z
          (derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫ k) =
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
              (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y) Z).symm k) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app (Opposite.op Y, Z)) := by
    intro k
    have hk := homEquiv_derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y Z
      (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y) Z).symm k)
    rw [AddEquiv.apply_symm_apply] at hk
    exact hk.symm
  have h1 := ((key h).symm.trans (congrArg
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ Z) hyp)).trans
      (key h')
  have h2 := ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
    max uR uA uM + 1} R).homEquiv X Y _).injective h1
  have h3 := (comp_natIso_inv_comp_natIso_hom.{uR, uA, uM} f F comparison Y Z _).symm.trans
    ((congrArg (fun z => z ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).hom.app (Opposite.op Y, Z)) h2).trans
      (comp_natIso_inv_comp_natIso_hom.{uR, uA, uM} f F comparison Y Z _))
  exact ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
    max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y) Z).symm.injective
      ((Equiv.apply_eq_iff_eq _).mp h3)

/-- `ν_{X,Y}` is a section of the lax monoidal structure map: `ν ≫ μ = 𝟙`. -/
theorem derivedTensorBaseChangeSection_comp_derivedTensorBaseChange
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y = 𝟙 _ := by
  have hchar := unit_comp_homEquiv_symm_derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y
  have hL := homEquiv_derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y
    (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (X, Y)))
    (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj X)
      (F.obj Y) _).symm (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y))
  rw [AddEquiv.apply_symm_apply, Adjunction.homEquiv_unit, hchar] at hL
  refine ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv _ _).injective ?_
  refine Eq.trans hL.symm ?_
  refine Eq.trans (congrArg (fun z =>
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y _ z)
      (comp_natIso_hom_comp_natIso_inv.{uR, uA, uM} f F comparison Y _ _)) ?_
  refine Eq.trans (AddEquiv.apply_symm_apply _ _) ?_
  simp [Adjunction.homEquiv_unit]

/-- `ν_{X,Y}` is a retraction of the lax monoidal structure map: `μ ≫ ν = 𝟙`. -/
theorem derivedTensorBaseChange_comp_derivedTensorBaseChangeSection
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ≫
        derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y = 𝟙 _ := by
  refine derivedTensorBaseChangeSection_comp_injective.{uR, uA, uM} f F comparison X Y _ ?_
  rw [← Category.assoc, derivedTensorBaseChangeSection_comp_derivedTensorBaseChange,
    Category.id_comp, Category.comp_id]

/-- Derived extension of scalars along a homomorphism of commutative rings is strongly monoidal
for the derived tensor products of the [stacks 0A63] bundles: the structure map
`Dualizing.derivedTensorBaseChange` is an isomorphism, with inverse
`Dualizing.derivedTensorBaseChangeSection`. -/
instance isIso_derivedTensorBaseChange
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    IsIso (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y) :=
  ⟨derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y,
    derivedTensorBaseChange_comp_derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y,
    derivedTensorBaseChangeSection_comp_derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y⟩

end Dualizing

end
