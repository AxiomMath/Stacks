module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.DerivedAdjunction

/-!
# The derived sheafification–global sections adjunction on an affine scheme

For a commutative ring `R`, derived sheafification
`AlgebraicGeometry.derivedTilde : D(R) ⥤ D_QCoh(𝒪_{Spec R})` is left adjoint to unbounded derived
global sections `RΓ(Spec R, -)`, and the adjunction is *canonically normalized*: its unit is the
degreewise sheafification–sections unit of `AlgebraicGeometry.tilde.adjunction` followed by the
canonical comparison from termwise global sections to derived global sections. That normalization
determines the adjunction, hence also its counit, which is why the adjunction is packaged here
together with it as a subtype.

The construction is the general derived adjunction of
`StacksFrontier/AlgebraicGeometry/DerivedTildeEquivalence/DerivedAdjunction.lean`, applied to the
exact left adjoint `M ↦ M̃` and the right derived functor of global sections.

## Main definitions

* `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` — **Stacks 06Z0**: the canonically
  normalized derived sheafification–sections adjunction on an affine scheme.

## Main results

* `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app` — the unit of that
  adjunction is invertible as soon as the degreewise comparison from global sections to derived
  global sections is invertible on complexes of the form `M̃^•`.

## Implementation notes

The two derived categories are taken at free `[HasDerivedCategory.{w₁} (Spec R).Modules]` and
`[HasDerivedCategory.{w₂} (ModuleCat.{u} R)]` binders, with independent morphism universes.
Nothing in the construction depends on the model: `Stacks.SmallDerivedCategory.derivedAdjunction`
has free binders, and the K-injective resolutions that feed it are a statement about cochain
complexes. The default a consumer gets, from `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
and `ModuleCat.hasDerivedCategory`, is the locally small model, which is the one Brown
representability needs; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`.

`AlgebraicGeometry.globalSectionsOver (𝟙 (Spec R))` and `AlgebraicGeometry.moduleSpecΓFunctor`
are equal, so `AlgebraicGeometry.tilde.adjunction` already *is* an adjunction between
`tilde.functor R` and the former; no transport along an isomorphism of functors is needed.

The unit and counit of this adjunction are invertible, which is the derived Spec–Γ equivalence;
that is not proved here. For the unit, `isIso_derivedTildeGlobalSectionsAdjunction_unit_app`
isolates exactly what is missing, namely affine vanishing for an unbounded complex of
quasi-coherent modules (Stacks 08D4).

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- **Stacks 06Z0.** The canonical derived sheafification–sections adjunction on an affine
scheme. Its unit is characterized by the degreewise sheafification–sections unit and the
right-derived comparison; thus the adjunction, including its counit, has the canonical
normalization. -/
-- NO `@[stacks 06Z0]` ATTRIBUTE HERE, DELIBERATELY -- but not because the tag is open: it is
-- proved. This adjunction is the ROUTE to the tag, not a clause of its statement; that its unit
-- and counit are invertible, which is what the tag asserts, is
-- `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit` and
-- `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` of
-- `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`, with
-- `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso` of
-- `StacksFrontier/AlgebraicGeometry/DerivedTildeCounit.lean`. The full covering set of the tag is
-- listed in the implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedTilde.lean`. An
-- attribute here would report 06Z0 a second time, on the strength of a definition.
def derivedTildeGlobalSectionsAdjunction :
    { adj : (derivedTilde R ⋙
        (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι) ⊣
        derivedGlobalSectionsOver (𝟙 (Spec R)) //
      ∀ M : CochainComplex (ModuleCat.{u} R) ℤ,
        adj.unit.app (DerivedCategory.Q.obj M) ≫
            (derivedGlobalSectionsOver (𝟙 (Spec R))).map
              ((derivedTildeFactors R).hom.app M) =
          DerivedCategory.Q.map ((tildeGlobalSectionsComplexUnit R).app M) ≫
            globalSectionsComplexComparison (𝟙 (Spec R))
              (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) } :=
  ⟨Stacks.SmallDerivedCategory.derivedAdjunction (G := globalSectionsOver (𝟙 (Spec R)))
      (tilde.adjunction (R := R)) (derivedTildeCompι R)
      (derivedGlobalSectionsOverUnit (𝟙 (Spec R)))
      (Scheme.Modules.exists_quasiIso_isKInjective (Spec R)),
    fun M => by
      rw [← globalSectionsComplexComparisonNatTrans_app]
      exact Stacks.SmallDerivedCategory.derivedAdjunction_unit_app_Q
        (G := globalSectionsOver (𝟙 (Spec R))) (tilde.adjunction (R := R))
        (derivedTildeCompι R) (derivedGlobalSectionsOverUnit (𝟙 (Spec R)))
        (Scheme.Modules.exists_quasiIso_isKInjective (Spec R)) M⟩

/-- **The derived Spec–Γ unit is invertible as soon as affine vanishing holds for unbounded
complexes.** The unit of `derivedTildeGlobalSectionsAdjunction` is invertible at every object of
`D(R)` provided the degreewise comparison `Q(Γ(Spec R, M̃^•)) ⟶ RΓ(Spec R, Q(M̃^•))` is invertible
for every cochain complex `M^•` of `R`-modules.

This is the whole remaining content of Stacks 06Z0's invertibility statements: the derived unit
differs from the degreewise sheafification–sections unit, which is invertible, only by that
comparison and by the comparison `derivedTildeFactors`, which is an isomorphism. The hypothesis
is affine vanishing for an *unbounded* complex, which is Stacks 08D4 and needs the
`E = Rlim τ_{≥-n}E` argument; for a single quasi-coherent module it is Serre vanishing,
Stacks 01XB. -/
theorem isIso_derivedTildeGlobalSectionsAdjunction_unit_app
    (h : ∀ M : CochainComplex (ModuleCat.{u} R) ℤ,
      IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
    (M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M) := by
  obtain ⟨M', ⟨eM⟩⟩ : DerivedCategory.Q.essImage M :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) M
  have hM' : IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app
      (DerivedCategory.Q.obj M')) := by
    have h₁ := h M'
    have h₂ : IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app
          (DerivedCategory.Q.obj M') ≫
        (derivedGlobalSectionsOver (𝟙 (Spec R))).map ((derivedTildeFactors R).hom.app M')) := by
      rw [(derivedTildeGlobalSectionsAdjunction R).2 M']
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).map ((derivedTildeFactors R).hom.app M'))
  have hnat := (derivedTildeGlobalSectionsAdjunction R).val.unit.naturality eM.hom
  have heq : (derivedTildeGlobalSectionsAdjunction R).val.unit.app M =
      inv eM.hom ≫ (derivedTildeGlobalSectionsAdjunction R).val.unit.app
          (DerivedCategory.Q.obj M') ≫
        ((derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
            (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι) ⋙
          derivedGlobalSectionsOver (𝟙 (Spec R))).map eM.hom := by
    rw [← hnat]
    simp
  rw [heq]
  infer_instance

end AlgebraicGeometry

end
