module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Additivity of the canonical Frobenius trace along an open and closed decomposition

Step 1 of the proof of [Stacks, Tag 03UG] in the form used on a compactification: for a scheme
`Y` over a finite field `k`, a closed immersion `i : Z ⟶ Y` with open complement `j : U ⟶ Y`, and a
bounded below complex `C` on `Y_étale`, the short exact sequence
`0 → j_! j^{-1} C → C → i_* i^{-1} C → 0` of [Stacks, Tag 095L] gives
`T''(Y, C) = T''(Y, j_! j^{-1} C) + T''(Y, i_* i^{-1} C)`.

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `openClosedCochainShortComplex`: the short complex `j_! j^{-1} C → C → i_* i^{-1} C` of
  complexes of sheaves of modules.

## Main results

* `openClosedCochainShortComplex_shortExact`: it is short exact.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_openClosed`:
  `T''(Y, C) = T''(Y, j_! j^{-1} C) + T''(Y, i_* i^{-1} C)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

section SES

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
  [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- The short complex `j_! j^{-1} C → C → i_* i^{-1} C` of complexes of sheaves of modules,
degreewise the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`. -/
def openClosedCochainShortComplex (C : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ) where
  X₁ := ((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex _).obj
    (((etaleModuleRestriction.{u, r} Λ j).mapHomologicalComplex _).obj C)
  X₂ := C
  X₃ := ((etaleModuleDirectImage.{u, r} Λ i).mapHomologicalComplex _).obj
    (((etaleModuleInverseImage.{u, r} Λ i).mapHomologicalComplex _).obj C)
  f :=
    { f := fun n => (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app (C.X n)
      comm' := fun a b _ =>
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.naturality (C.d a b)).symm }
  g :=
    { f := fun n => (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app (C.X n)
      comm' := fun a b _ =>
        ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.naturality (C.d a b)).symm }
  zero := by
    ext n : 1
    exact etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij (C.X n)

include hij in
/-- The short complex `j_! j^{-1} C → C → i_* i^{-1} C` is short exact. -/
lemma openClosedCochainShortComplex_shortExact (C : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (openClosedCochainShortComplex Λ i j hij C).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (shortExact_etaleModuleExtensionByZero_directImage Λ i j hij (C.X n)).2

end SES

section Frobenius

variable {Z U : Scheme.{u}} {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (i : Z ⟶ Y.left)
  [IsClosedImmersion i] (j : U ⟶ Y.left) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

include hij in
/-- **Step 1 of [Stacks, Tag 03UG] for an open and closed decomposition.**  For a closed
immersion `i : Z ⟶ Y` with open complement `j : U ⟶ Y` and a bounded below complex `C` on
`Y_étale`, with the three cohomologies perfect,
`T''(Y, C) = T''(Y, j_! j^{-1} C) + T''(Y, i_* i^{-1} C)`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_openClosed
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C))))))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))) +
        CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₃⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C)))) :=
  perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_X₂_eq_add Λ Y kbar p q hcard
    (openClosedCochainShortComplex_shortExact Λ i j hij C.obj)
    ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
      ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)).property C.property
    ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C)).property hp₁ hp₂ hp₃

end Frobenius

end Stacks.EtaleCohomology

end
