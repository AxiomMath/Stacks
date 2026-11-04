module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormula
import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso

/-!
# The component formula for the projection formula

`Dualizing.ProjectionFormula.derivedProjNatIso` is descended from a family of comparisons
indexed by the K-flat complexes of `A`-modules, through
`ModuleSystemRlimTensor.natIsoOfResolutions`, whose components are conjugated from the component
at a chosen resolution. This file evaluates the projection formula at the class of a K-flat
complex, and from there at the chain level, through the five pasted comparisons of
`Dualizing.ProjectionFormula.derivedProjKFlatChain`.

## Main results

* `ModuleSystemRlimTensor.natIsoOfResolutions_hom_app_of_prop` — the component formula for
  `ModuleSystemRlimTensor.natIsoOfResolutions` at a complex of the resolving class.  This is the
  isomorphism-valued form of `Dualizing.natTransOfResolutions_app_of_prop`.
* `Dualizing.ProjectionFormula.derivedProjBifunctorNatIso_hom_app_kFlat` — the bifunctorial
  projection formula at the class of a K-flat complex is the comparison
  `Dualizing.ProjectionFormula.derivedProjKFlatRep` the descent was fed.
* `Dualizing.ProjectionFormula.derivedProjNatIso_hom_kFlat` — the same for
  `derivedProjNatIso`, and `derivedProjNatIso_inv_kFlat` for its inverse.
* `Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q` — **the chain-level component
  formula.**  At a K-flat representative `P` of the object of `D(A)` and an arbitrary
  representative `L` of the object of `D(B)`, the projection formula is the model comparison at
  `P`, the identification of `iStar` with derived restriction of scalars, the five pasted
  chain-level comparisons of `derivedProjKFlatChain`, and that identification again.

## The coherences of [Stacks, Tag 0E2H]

[Stacks, Tag 0E2H] still needs two coherences of the projection formula. The first is that the
counit `ε` of extension ⊣ restriction (Stacks 0GMT) is compatible with it and with the lax
monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base change:

`μ_{i_*F, N} ≫ Ext(derivedProjNatIso_N.inv.app F) ≫ ε_{F ⊗ᴸ_B Ext N} = ε_F ⊗ᴸ_B 𝟙_{Ext N}`

as morphisms `Ext(i_*F) ⊗ᴸ_B Ext N ⟶ F ⊗ᴸ_B Ext N`. The other two factors are known at
representatives: the counit by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`, and
`Dualizing.derivedTensorBaseChange` by its mate characterisation
`Dualizing.derivedTensorBaseChange_mate`; `derivedProjNatIso_hom_app_Q` is the value of the
projection formula there. The equation is `Dualizing.ProjectionFormula.ProjCounitCompat` in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit`, where
`projCounitCompat_iff` transposes the structure map away and `projCounitCompat_of_kFlat` reduces
it to the class of a K-flat complex and the class of an arbitrary complex.

The second is `Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge`, which
`Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCanonical` reduces, granted the
first, to a coherence of the lax monoidal structure map in which the projection formula does not
occur.

## Implementation notes

`ModuleSystemRlimTensor.natIsoOfResolutions` is `CategoryTheory.asIso` of
`ModuleSystemRlimTensor.natTransOfResolutions`, so its forward direction *is* the descended
transformation and the component formula `Dualizing.natTransOfResolutions_app_of_prop` (a
descended transformation is the given family at a complex of the resolving class) applies to it
unchanged.

No `@[stacks]` attribute is placed here: these are component formulas for the isomorphism of
[Stacks, Tag 0E9L] constructed in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormula`, which is where the tag sits.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleSystemRlimTensor

/-- **The component formula for `ModuleSystemRlimTensor.natIsoOfResolutions`** at a complex of
the resolving class: there the descended isomorphism is the given family, with no conjugation by
a resolution. -/
theorem natIsoOfResolutions_hom_app_of_prop {B D : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ≅ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ (e L hL).hom =
        (e K hK).hom ≫ G.map (DerivedCategory.Q.map f))
    (K : CochainComplex B ℤ) (hK : P K) :
    (natIsoOfResolutions P hP F G e he).hom.app (DerivedCategory.Q.obj K) = (e K hK).hom :=
  Dualizing.natTransOfResolutions_app_of_prop P hP F G (fun K hK => (e K hK).hom) he K hK

/-- The inverse direction of `ModuleSystemRlimTensor.natIsoOfResolutions` at a complex of the
resolving class. -/
theorem natIsoOfResolutions_inv_app_of_prop {B D : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ≅ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ (e L hL).hom =
        (e K hK).hom ≫ G.map (DerivedCategory.Q.map f))
    (K : CochainComplex B ℤ) (hK : P K) :
    (natIsoOfResolutions P hP F G e he).inv.app (DerivedCategory.Q.obj K) = (e K hK).inv :=
  congrArg Iso.inv (Iso.ext (natIsoOfResolutions_hom_app_of_prop P hP F G e he K hK) :
    (natIsoOfResolutions P hP F G e he).app (DerivedCategory.Q.obj K) = e K hK)

end ModuleSystemRlimTensor

namespace Dualizing.ProjectionFormula

open CochainComplex CochainComplex.DerivedTensor CochainComplex.KFlat.ScalarBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The projection formula at a K-flat representative.**  The bifunctorial form of the
projection formula, evaluated at the class of a K-flat complex `P` of `A`-modules, is the
comparison `Dualizing.ProjectionFormula.derivedProjKFlatRep` at `P` itself. -/
theorem derivedProjBifunctorNatIso_hom_app_kFlat (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    (derivedProjBifunctorNatIso.{u, v} φ E iStar adj).hom.app (DerivedCategory.Q.obj P) =
      (derivedProjKFlatRep.{u, v} φ E iStar adj P hP).hom :=
  ModuleSystemRlimTensor.natIsoOfResolutions_hom_app_of_prop _ _ _ _ _ _ P hP

/-- `Dualizing.ProjectionFormula.derivedProjNatIso` at the class of a K-flat complex. -/
theorem derivedProjNatIso_hom_kFlat (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    (derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).hom =
      (derivedProjKFlatRep.{u, v} φ E iStar adj P hP).hom :=
  derivedProjBifunctorNatIso_hom_app_kFlat.{u, v} φ E iStar adj P hP

/-- The inverse of `Dualizing.ProjectionFormula.derivedProjNatIso` at the class of a K-flat
complex. -/
theorem derivedProjNatIso_inv_kFlat (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    (derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).inv =
      (derivedProjKFlatRep.{u, v} φ E iStar adj P hP).inv :=
  ModuleSystemRlimTensor.natIsoOfResolutions_inv_app_of_prop _ _ _ _ _ _ P hP

/-- **The projection formula at a K-flat representative, at an object of `D(B)`.** At the class
of a K-flat complex `P` of `A`-modules and an object `X` of `D(B)`, the projection formula is the
model comparison at `P`, the identification of `iStar` with derived restriction of scalars, the
component of `Dualizing.ProjectionFormula.derivedProjKFlat` at `X`, and that identification
again. -/
theorem derivedProjNatIso_hom_app (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P)
    (X : DerivedCategory (ModuleCat.{max u v} B)) :
    (derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).hom.app X =
      iStar.map
          (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
            max u v + 1} B).tensor).flip.map (E.comparison.app P)).app X) ≫
        (leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).hom.app
            ((tensorRightDerived.{u, v} B
              (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P))).obj X) ≫
          (derivedProjKFlat.{u, v} φ P hP).hom.app X ≫
            (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
              ((leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).inv.app X) := by
  rw [derivedProjNatIso_hom_kFlat.{u, v} φ E iStar adj P hP]
  rfl

/-- **The chain-level component formula for the projection formula.**  At the class of a K-flat
complex `P` of `A`-modules and the class of an arbitrary complex `L` of `B`-modules, the
projection formula is the model comparison at `P`, the identification of `iStar` with derived
restriction of scalars, the five pasted chain-level comparisons of
`Dualizing.ProjectionFormula.derivedProjKFlatChain`, and that identification again. -/
theorem derivedProjNatIso_hom_app_Q (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P)
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).hom.app
        (DerivedCategory.Q.obj L) =
      iStar.map
          (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
            max u v + 1} B).tensor).flip.map (E.comparison.app P)).app
            (DerivedCategory.Q.obj L)) ≫
        (leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).hom.app
            ((tensorRightDerived.{u, v} B
              (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P))).obj
              (DerivedCategory.Q.obj L)) ≫
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P)
                (isKFlat_extendScalarsLarge.{u, v} φ P hP)).hom ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
                ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L) ≫
              DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P L).hom ≫
                (derivedTensor_comparison.{u, v} A
                  ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).inv ≫
                  (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
                    ((ModuleCat.restrictScalars.{max u v}
                      φ).mapDerivedCategoryFactors.inv.app L)) ≫
            (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
              ((leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).inv.app
                (DerivedCategory.Q.obj L)) := by
  rw [derivedProjNatIso_hom_app.{u, v} φ E iStar adj P hP, derivedProjKFlat_hom_app_Q,
    derivedProjKFlatChain_hom_app]

end Dualizing.ProjectionFormula

end
