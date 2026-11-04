module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentKernels

/-!
# The unit and the counit of `Lε^* ⊣ Rε_*` are the abelian ones, degreewise

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 070R/08H7.  `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction` is the derived
adjunction `Lε^* ⊣ Rε_*` on the unbounded derived categories, and its unit and counit are already
identified there with the ones induced by the unit and counit of `ε^* ⊣ ε_*` together with the two
derived-functor comparison maps.  Those identifications are stated on the *homotopy* category, at
an object of `K(𝒪_S)` resp. `K(S_étale, 𝒪)`; this file reads them at a cochain complex, where the
abelian unit and counit of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` appear degreewise, and draws the
consequence the derived adjunction is used for:

**the derived unit and counit are invertible as soon as the abelian ones are invertible in every
degree and the comparison `ε_* ⟶ Rε_*` is invertible on the complex at hand.**

For the unit the abelian half is `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent` and for the
counit it is `AlgebraicGeometry.SmallEtale.isIso_counit'`; both are proved
and unconditional, so what is left on each side is exactly the invertibility of the comparison at
`ε^* M` resp. at the complex itself — the acyclicity input of Stacks 071Q, and the only thing
these statements ask of their caller.

## The passage from `K` to complexes

`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction_unit_app` mentions
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction`, whose unit and counit are
`CategoryTheory.Quotient.natTransLift`s and therefore say nothing about a complex until they are
unfolded at the class of one.  That unfolding holds by definition — it is
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient`, which is proved by
`rfl` — and performing it is all that `derivedAssociatedModuleAdjunction_unit_app_quotient` below
does; the two statements are definitionally equal, so that theorem is the library's one applied at
the class of `M` and nothing more.  With the unfolding done, the degreewise unit
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction` is in the statement, and its component
in degree `n` *is* the abelian unit at the degree-`n` term, so a degreewise hypothesis on the
abelian unit becomes usable.  (The two `quotient` lemmas are not *rewritten* with: their
`CategoryTheory.Preadditive` instance arguments are synthesized along a different path than the
ones in these goals, so `rw` does not match them, while `exact` sees through the difference.)

## Main results

* `derivedAssociatedModuleAdjunction_unit_app_quotient` and
  `derivedAssociatedModuleAdjunction_counit_app_quotient`: the unit and the counit of
  `Lε^* ⊣ Rε_*` at the image of a cochain complex, in terms of the *degreewise* unit and counit
  of `ε^* ⊣ ε_*` and the two comparison maps.
* `isIso_derivedAssociatedModuleAdjunction_unit_app_degreewise` and
  `isIso_derivedAssociatedModuleAdjunction_counit_app_degreewise`: **the degreewise criterion** —
  the derived unit resp. counit is invertible at a complex whose abelian unit resp. counit is
  invertible in every degree and at which the comparison `ε_* ⟶ Rε_*` is invertible.
* `isIso_derivedAssociatedModuleAdjunction_unit_app_of_isQuasicoherent` and
  `isIso_derivedAssociatedModuleAdjunction_counit_app_of_isQuasicoherentOnSite`: the same with
  the abelian half discharged from quasi-coherence of the terms.
* `isIso_derivedAssociatedModuleAdjunction_unit_app_of_isKInjective` and
  `isIso_derivedAssociatedModuleAdjunction_counit_app_of_isKInjective`: the same with the
  comparison half discharged as well, from K-injectivity. These assume nothing beyond the two
  `CategoryTheory.HasDerivedCategory` instances.

## What is not here

The two criteria are *not* phrased through the cohomology objects: there is no claim that
`Hⁿ(η_K)` is the abelian unit at `Hⁿ(K)`.  Such a claim needs a comparison
`Hⁿ(Rε_* E) ⟶ ε_*(Hⁿ E)` for the right derived functor — `ε_*` is not exact, so `Hⁿ ∘ Rε_*` and
`ε_* ∘ Hⁿ` are different functors and the identification is the edge transformation
`Stacks.DerivedFunctor.homologyEdge`, read at `ε`.  The criteria below are what the degreewise
check actually consumes, and they avoid that comparison entirely: invertibility of a map of
`D(𝒪_S)` is tested against the complexes representing it, not against its cohomology.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-! ### The unit -/

/-- **The unit of `Lε^* ⊣ Rε_*` at a cochain complex of `𝒪_S`-modules.**  Composed with the
comparison for `Lε^*`, it is the *degreewise* unit of `ε^* ⊣ ε_*` followed by the comparison
`ε_* ⟶ Rε_*`.

This is `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction_unit_app` with the unit of
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction` unfolded at the class of `M`, which is
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient` and holds by `rfl`. -/
theorem derivedAssociatedModuleAdjunction_unit_app_quotient
    (M : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) :
    (derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
              (ComplexShape.up ℤ)).obj M)) ≫
        (derivedRestrictModule.{w, w} B S hS).map
          ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
              (ComplexShape.up ℤ)).obj M)) =
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
            (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
              (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M)) ≫
        (derivedRestrictModuleUnit.{w, w} B S hS).app
          (((associatedModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
              (ComplexShape.up ℤ)).obj M)) :=
  derivedAssociatedModuleAdjunction_unit_app.{w} B S hS _

/-- **The degreewise criterion for the unit.**  The unit of `Lε^* ⊣ Rε_*` is invertible at the
image in `D(𝒪_S)` of a cochain complex `M` as soon as

* the unit of `ε^* ⊣ ε_*` is invertible at every term of `M`, and
* the comparison `ε_* (ε^* M) ⟶ Rε_* (ε^* M)` is invertible.

The first hypothesis holds for a complex of quasi-coherent modules, by
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`; the second is the acyclicity of `ε^* M` for
`ε_*`, and it is all that is asked of the caller. -/
theorem isIso_derivedAssociatedModuleAdjunction_unit_app_degreewise
    (M : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (hM : ∀ n : ℤ, IsIso ((associatedModuleAdjunction B S hS).unit.app (M.X n)))
    (hcomp : IsIso ((derivedRestrictModuleUnit.{w, w} B S hS).app
      (((associatedModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ)).obj M)))) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
      (DerivedCategory.Q.obj M)) := by
  have hu : IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
      (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M) := by
    have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
        (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M).f n) := hM
    exact HomologicalComplex.Hom.isIso_of_components _
  have hqh : IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ)).obj M))) := by
    have := hu
    have hq : IsIso ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
        (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction
            (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
            (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M)) :=
      Functor.map_isIso _ _
    have := hq
    have hqq : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
              (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M))) :=
      Functor.map_isIso _ _
    have hfac : IsIso ((derivedRestrictModule.{w, w} B S hS).map
        ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
            (ComplexShape.up ℤ)).obj M))) :=
      Functor.map_isIso _ _
    have h := derivedAssociatedModuleAdjunction_unit_app_quotient.{w} B S hS M
    have : IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
            (ComplexShape.up ℤ)).obj M)) ≫
          (derivedRestrictModule.{w, w} B S hS).map
            ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
                (ComplexShape.up ℤ)).obj M))) := by
      rw [h]
      exact IsIso.comp_isIso' hqq hcomp
    exact IsIso.of_isIso_comp_right _ ((derivedRestrictModule.{w, w} B S hS).map
      ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ)).obj M)))
  rw [← NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} S.ringCatSheaf)).app M)]
  exact hqh

/-- **The degreewise criterion for the unit, at a complex of quasi-coherent modules.** The
abelian half of `isIso_derivedAssociatedModuleAdjunction_unit_app_degreewise` discharged by
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, the small-site half of Stacks 0GN7 at
`τ = étale`. -/
theorem isIso_derivedAssociatedModuleAdjunction_unit_app_of_isQuasicoherent
    (M : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (hM : ∀ n : ℤ, SheafOfModules.isQuasicoherent S.ringCatSheaf (M.X n))
    (hcomp : IsIso ((derivedRestrictModuleUnit.{w, w} B S hS).app
      (((associatedModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ)).obj M)))) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
      (DerivedCategory.Q.obj M)) :=
  isIso_derivedAssociatedModuleAdjunction_unit_app_degreewise.{w} B S hS M
    (fun n => unitIsoOnQuasicoherent B S hS ⟨M.X n, hM n⟩) hcomp

/-- **The unit of `Lε^* ⊣ Rε_*` is invertible at a complex of quasi-coherent modules whose
associated module is K-injective.**  The comparison hypothesis of
`AlgebraicGeometry.SmallEtale.isIso_derivedAssociatedModuleAdjunction_unit_app_of_isQuasicoherent`
discharged by the second assertion of Stacks 07A5 at `ε`,
`AlgebraicGeometry.SmallEtale.isIso_derivedRestrictModuleUnit_app_of_isKInjective`: a K-injective
complex computes `Rε_*`.

This is the one unconditional instance available with no acyclicity input: nothing is assumed
beyond the two `CategoryTheory.HasDerivedCategory` instances. -/
theorem isIso_derivedAssociatedModuleAdjunction_unit_app_of_isKInjective
    (M : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (hM : ∀ n : ℤ, SheafOfModules.isQuasicoherent S.ringCatSheaf (M.X n))
    (hK : CochainComplex.IsKInjective
      (((associatedModuleOfSheaf B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app
      (DerivedCategory.Q.obj M)) :=
  isIso_derivedAssociatedModuleAdjunction_unit_app_of_isQuasicoherent.{w} B S hS M hM
    (isIso_derivedRestrictModuleUnit_app_of_isKInjective.{w} B S hS _ hK)

/-! ### The counit -/

/-- **The counit of `Lε^* ⊣ Rε_*` at a cochain complex of `𝒪`-modules on `S_étale`.**  Precomposed
with `Lε^*` of the comparison `ε_* ⟶ Rε_*`, it is the comparison for `Lε^*` followed by the
*degreewise* counit of `ε^* ⊣ ε_*`.

This is `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction_counit_app` with the
counit of `CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction` unfolded at the class of `E`,
which is `CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_counit_app_quotient` and holds
by `rfl`. -/
theorem derivedAssociatedModuleAdjunction_counit_app_quotient
    (E : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) :
    (associatedModuleOfSheaf B S hS).mapDerivedCategory.map
          ((derivedRestrictModuleUnit.{w, w} B S hS).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
              (ComplexShape.up ℤ)).obj E)) ≫
        (derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
              (ComplexShape.up ℤ)).obj E)) =
      (associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
          (((restrictModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
              (ComplexShape.up ℤ)).obj E)) ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
            (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
              (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app E)) :=
  derivedAssociatedModuleAdjunction_counit_app.{w} B S hS _

/-- **The degreewise criterion for the counit.**  The counit of `Lε^* ⊣ Rε_*` is invertible at the
image in `D(S_étale, 𝒪)` of a cochain complex `E` as soon as

* the counit of `ε^* ⊣ ε_*` is invertible at every term of `E`, and
* the comparison `ε_* E ⟶ Rε_* E` is invertible.

The first hypothesis holds for a complex of quasi-coherent modules on `S_étale`, by
`AlgebraicGeometry.SmallEtale.isIso_counit'`; the second is the acyclicity
of `E` for `ε_*`, and it is all that is asked of the caller. -/
theorem isIso_derivedAssociatedModuleAdjunction_counit_app_degreewise
    (E : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (hE : ∀ n : ℤ, IsIso ((associatedModuleAdjunction B S hS).counit.app (E.X n)))
    (hcomp : IsIso ((derivedRestrictModuleUnit.{w, w} B S hS).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
        (ComplexShape.up ℤ)).obj E))) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
      (DerivedCategory.Q.obj E)) := by
  have hc : IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
      (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app E) := by
    have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
        (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app E).f n) := hE
    exact HomologicalComplex.Hom.isIso_of_components _
  have hqh : IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
          (ComplexShape.up ℤ)).obj E))) := by
    have := hc
    have := hcomp
    have hcomp' : IsIso ((associatedModuleOfSheaf B S hS).mapDerivedCategory.map
        ((derivedRestrictModuleUnit.{w, w} B S hS).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
            (ComplexShape.up ℤ)).obj E))) :=
      Functor.map_isIso _ _
    have hq : IsIso ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
        (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction
            (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
            (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app E)) :=
      Functor.map_isIso _ _
    have := hq
    have hqq : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
          (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
              (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app E))) :=
      Functor.map_isIso _ _
    have hfac : IsIso ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
        (((restrictModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
            (ComplexShape.up ℤ)).obj E))) :=
      inferInstance
    have h := derivedAssociatedModuleAdjunction_counit_app_quotient.{w} B S hS E
    have : IsIso ((associatedModuleOfSheaf B S hS).mapDerivedCategory.map
          ((derivedRestrictModuleUnit.{w, w} B S hS).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
              (ComplexShape.up ℤ)).obj E)) ≫
        (derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
              (ComplexShape.up ℤ)).obj E))) := by
      rw [h]
      exact IsIso.comp_isIso' hfac hqq
    exact IsIso.of_isIso_comp_left ((associatedModuleOfSheaf B S hS).mapDerivedCategory.map
      ((derivedRestrictModuleUnit.{w, w} B S hS).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
          (ComplexShape.up ℤ)).obj E))) _
  rw [← NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheaf B S hS))).app E)]
  exact hqh

/-- **The degreewise criterion for the counit, at a complex of quasi-coherent modules on
`S_étale`.** The abelian half of `isIso_derivedAssociatedModuleAdjunction_counit_app_degreewise`
discharged by `AlgebraicGeometry.SmallEtale.isIso_counit'`. -/
theorem isIso_derivedAssociatedModuleAdjunction_counit_app_of_isQuasicoherentOnSite
    (E : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (hE : ∀ n : ℤ, (E.X n).IsQuasicoherentOnSite)
    (hcomp : IsIso ((derivedRestrictModuleUnit.{w, w} B S hS).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B S hS))
        (ComplexShape.up ℤ)).obj E))) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
      (DerivedCategory.Q.obj E)) :=
  isIso_derivedAssociatedModuleAdjunction_counit_app_degreewise.{w} B S hS E
    (fun n => isIso_counit' B S hS (E.X n) (hE n)) hcomp

/-- **The counit of `Lε^* ⊣ Rε_*` is invertible at a K-injective complex of quasi-coherent
modules on `S_étale`.** The comparison hypothesis of
`isIso_derivedAssociatedModuleAdjunction_counit_app_of_isQuasicoherentOnSite` discharged by the
second assertion of Stacks 07A5 at `ε`,
`AlgebraicGeometry.SmallEtale.isIso_derivedRestrictModuleUnit_app_of_isKInjective`.

Nothing is assumed beyond the two `CategoryTheory.HasDerivedCategory` instances. -/
theorem isIso_derivedAssociatedModuleAdjunction_counit_app_of_isKInjective
    (E : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (hE : ∀ n : ℤ, (E.X n).IsQuasicoherentOnSite) (hK : E.IsKInjective) :
    IsIso ((derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
      (DerivedCategory.Q.obj E)) :=
  isIso_derivedAssociatedModuleAdjunction_counit_app_of_isQuasicoherentOnSite.{w} B S hS E hE
    (isIso_derivedRestrictModuleUnit_app_of_isKInjective.{w} B S hS E hK)

end AlgebraicGeometry.SmallEtale

end
