module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedReduction
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence

/-!
# Clause (3) of Stacks 0FUU from the vanishing of the higher direct images of a kernel

For a morphism `b : L ⟶ X` and a closed immersion `j : E ⟶ L`, the restriction of forms
`Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}` is surjective.  So
`H^q(Rb_*(Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}))` is invertible for every `q ≥ 1` as soon as the higher direct
images along `b` of its kernel vanish.  This is the reduction the source's proof of clause (3) of
[Stacks, Tag 0FUR] uses.

## Main results

* `Stacks.DeRham.isIso_homology_derivedPushforward_map_of_shortExact`: for a short exact sequence
  `0 → K → F → F' → 0` with `H^q(Rb_* K) = 0` for `q ≥ 1`, the map `H^q(Rb_* F) ⟶ H^q(Rb_* F')` is
  an isomorphism for `q ≥ 1`.  This is the long exact sequence of the distinguished triangle of
  the short exact sequence, pushed forward by the triangulated functor `Rb_*`.
* `Stacks.DeRham.epi_relativeDifferentialFormsMap_of_isClosedImmersion` and
  `Stacks.DeRham.epi_formsDirectImageComparison_of_isClosedImmersion`: for a closed immersion
  `j`, both `j^*Ω^a_{L/S} ⟶ Ω^a_{E/S}` and `Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}` are epimorphisms.
* `Stacks.DeRham.isIso_formsRestrictionHomology_of_kernel`: the two together.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SchemeCohomology (hom)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- **Higher direct images of a surjection with acyclic kernel.**  For a short exact sequence
`0 → K → F → F' → 0` of modules on `L` with `H^q(Rb_* K) = 0` for every `q ≥ 1`, the map
`H^q(Rb_* F) ⟶ H^q(Rb_* F')` is an isomorphism for every `q ≥ 1`. -/
theorem isIso_homology_derivedPushforward_map_of_shortExact {L X : Scheme.{u}} (b : L ⟶ X)
    {S : ShortComplex L.Modules} (hS : S.ShortExact)
    (hK : ∀ q : ℤ, 1 ≤ q → IsZero ((DerivedCategory.homologyFunctor X.Modules q).obj
      ((schemeDerivedPushforward b).obj ((DerivedCategory.singleFunctor L.Modules 0).obj S.X₁))))
    {q : ℤ} (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
      ((schemeDerivedPushforward b).map
        ((DerivedCategory.singleFunctor L.Modules 0).map S.g))) := by
  let : (derivedPushforward (hom b)).CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift (derivedPushforward (hom b))
      (derivedPushforwardUnit (hom b))
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing (Stacks.SchemeCohomology.ringedSpace L)))
        (ComplexShape.up ℤ)) ℤ
  let : (derivedPushforward (hom b)).IsTriangulated := by
    have _ := SheafOfModules.isGrothendieckAbelianU
      (structureSheafRing (Stacks.SchemeCohomology.ringedSpace L))
    exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward (hom b))
      (derivedPushforward (hom b)) (derivedPushforwardUnit (hom b))
  have hS' := hS.map_of_exact (HomologicalComplex.single L.Modules (ComplexShape.up ℤ) 0)
  have hT := (derivedPushforward (hom b)).map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hS')
  set T := (derivedPushforward (hom b)).mapTriangle.obj (DerivedCategory.triangleOfSES hS')
  have hmono : Mono ((DerivedCategory.homologyFunctor X.Modules q).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT q).2
      ((hK q hq).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor X.Modules q).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT q (q + 1)).2
      ((hK (q + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor X.Modules q).map T.mor₂)

/-- For a closed immersion `j`, the canonical map `j^*Ω^a_{L/S} ⟶ Ω^a_{E/S}` is an epimorphism:
it is the `a`-th exterior power of the epimorphism `j^*Ω_{L/S} ⟶ Ω_{E/S}`
([Stacks, Tag 01CJ]). -/
theorem epi_relativeDifferentialFormsMap_of_isClosedImmersion {E L S : Scheme.{u}} (j : E ⟶ L)
    [IsClosedImmersion j] (p : L ⟶ S) (a : ℕ) :
    Epi (Scheme.Hom.relativeDifferentialFormsMap j p (j ≫ p) (𝟙 S) (by simp) (a : ℤ)) := by
  have hc : j ≫ p = (j ≫ p) ≫ 𝟙 S := by simp
  have he := Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap j p hc
  have h : Epi ((Scheme.Hom.relativeDifferentialFormsComparison j p (j ≫ p) (𝟙 S)
      hc).app (a : ℤ)) :=
    @_root_.SheafOfModules.ExtPresentation.epi_extDesc_app _ _ _ _ _ _
      (Scheme.Modules.exteriorGenerator _) (Scheme.Modules.exteriorGenerator _)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
      (Scheme.Hom.relativeDifferentialsMap j p (j ≫ p) (𝟙 S) hc) he a
  unfold Scheme.Hom.relativeDifferentialFormsMap
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) h

/-- **The restriction of forms to a closed subscheme is surjective**: for a closed immersion
`j : E ⟶ L`, the map `Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}` is an epimorphism. -/
theorem epi_formsDirectImageComparison_of_isClosedImmersion {E L S : Scheme.{u}} (j : E ⟶ L)
    [IsClosedImmersion j] (p : L ⟶ S) (a : ℕ) :
    Epi (Scheme.Hom.formsDirectImageComparison j p (a : ℤ)) := by
  have := Stacks.ClosedImmersion.epi_unit_app j (Scheme.Hom.relativeDifferentialForms p a)
  have := epi_relativeDifferentialFormsMap_of_isClosedImmersion j p a
  have : Epi ((Scheme.Modules.pushforward j).map
      (Scheme.Hom.relativeDifferentialFormsMap j p (j ≫ p) (𝟙 S) (by simp) (a : ℤ))) :=
    have := Stacks.ClosedImmersion.preservesEpimorphisms_pushforward j
    inferInstance
  exact epi_comp' inferInstance this

/-- **Clause (3) from the vanishing of the higher direct images of the kernel.**  For a closed
immersion `j : E ⟶ L`, the restriction `Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}` is surjective, so if the higher
direct images along `b` of its kernel vanish, then
`H^q(Rb_*(Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}))` is invertible for every `q ≥ 1`. -/
theorem isIso_formsRestrictionHomology_of_kernel {X L E S : Scheme.{u}} (b : L ⟶ X)
    (j : E ⟶ L) [IsClosedImmersion j] (p : L ⟶ S) (a : ℕ)
    (hK : ∀ q : ℤ, 1 ≤ q → IsZero ((DerivedCategory.homologyFunctor X.Modules q).obj
      ((schemeDerivedPushforward b).obj ((DerivedCategory.singleFunctor L.Modules 0).obj
        (kernel (Scheme.Hom.formsDirectImageComparison j p (a : ℤ)))))))
    {q : ℤ} (hq : 1 ≤ q) : IsIso (formsRestrictionHomology b j p a q) := by
  have := epi_formsDirectImageComparison_of_isClosedImmersion j p a
  have hS : (ShortComplex.mk (kernel.ι (Scheme.Hom.formsDirectImageComparison j p (a : ℤ)))
      (Scheme.Hom.formsDirectImageComparison j p (a : ℤ)) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  exact isIso_homology_derivedPushforward_map_of_shortExact b hS hK hq

end Stacks.DeRham
