module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionDerivedForget
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of modules along the projection `Δ × C ⟶ C`

Let `C` be a site, let `O` be a sheaf of rings on `C` and let `π : Δ × C ⥤ C` be the projection,
with `Δ × C` carrying the topology inherited from `C`. Remark 09CY specializes Lemma 08PC to
`π`: lower shriek `π_! : Mod(π^{-1}O) ⥤ Mod(O)` has a left derived functor
`Lπ_! : D(Δ × C, π^{-1}O) ⥤ D(O)`, left adjoint to `π^{-1}` on derived categories. This is the
second factor of the functor of Remark 09D3.

## Main results

* `Stacks.SimplicialModules.lowerShriekModules_acyclic`: the acyclicity statement of Stacks 07AC
  for `π_!` on modules.
* `Stacks.SimplicialModules.derivedModuleLowerShriek`: `Lπ_! : D(π^{-1}O) ⥤ D(O)`, with its
  adjunction to derived restriction, its commutation with shifts, and its exactness.
* `Stacks.SimplicialModules.derivedModuleLowerShriekForgetIso`: forgetting the module structure,
  `Lπ_!` on modules is `Lπ_!` on abelian sheaves (`forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`), the
  second assertion of Remark 09CY.

## Implementation notes

Everything is the specialization to the projection `π : Δ × C ⥤ C` of the general results for
the projection of a fibred category, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionDerivedForget.lean`:
the Stacks 07AC acyclicity statement for modules, read off from the abelian Stacks 0D6X along `π`,
and Stacks 08PC part (4). The fibred-category situation is `simplicialSituation (auxRingedSite J)`,
whose base structure sheaf plays no role. `O` is an arbitrary `RingCat`-valued sheaf, as in
Stacks 09D1.

The site is small: its objects, its morphisms, the sheaf of rings and the module sections all lie
in one universe `u`, as the sites of the source are.

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Sites.FibredCategory Stacks.Cohomology.DerivedLowerShriek

universe u

/- The abelian structure on sheaves of modules is the library's canonical
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`, the one the derived functors used
here are built with; the alternative instance of `SiteModules` would produce a different derived
category. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The projection is cocontinuous for the inherited topology, being a fibred category. -/
instance projection_isCocontinuous :
    (simplicialProjection (C := C)).IsCocontinuous (simplicialProjectionTopology J) J :=
  isCocontinuous_inheritedTopology_of_isFibered _ J

/-- The site `C` as a ringed site; its structure sheaf, which lower shriek on abelian sheaves does
not use, is the terminal sheaf of commutative rings. Reducible, unlike `auxRingedSite`, so that
the underlying category of the base of `projectionSituation` is `C` for instance search. -/
abbrev projectionRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := C
  J := J
  O := ⊤_ (Sheaf J CommRingCat.{u})

/-- The projection `π : Δ × C ⥤ C` as the fibred-category situation of Stacks 08P8 on which the
general results are stated. It is `simplicialSituation (auxRingedSite J)` (`rfl`). -/
abbrev projectionSituation : FibredCategorySituation.{u, u, u, u, u} where
  base := projectionRingedSite J
  C := SimplexCategory × C
  p := simplicialProjection

/-- `projectionSituation J` is the simplicial situation of `auxRingedSite J`. -/
theorem projectionSituation_eq : projectionSituation J = simplicialSituation (auxRingedSite J) :=
  rfl

variable (O : Sheaf J RingCat.{u})

/-- The sheaf of rings `π^{-1}O` on `Δ × C`. -/
abbrev simplicialProjectionRing : Sheaf (simplicialProjectionTopology J) RingCat.{u} :=
  inverseImageRing (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O

/-- **The acyclicity statement of Stacks 07AC for `π_!` on modules.** Lower shriek
`π_! : Mod(π^{-1}O) ⥤ Mod(O)` carries every bounded above acyclic complex whose terms are direct
sums of the `j_{U!} O_U` to an acyclic complex. This is
`FibredCategorySituation.lowerShriekModules_acyclic` for the projection. -/
theorem lowerShriekModules_acyclic (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (simplicialProjectionRing J O)) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits (simplicialProjectionRing J O) (L.X n))
    (hLac : L.Acyclic) :
    (((SheafOfModules.pullback.{u}
      (idRingMap (simplicialProjectionTopology J) J
          (simplicialProjection (C := C)) O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic :=
  (projectionSituation J).lowerShriekModules_acyclic O a L hLE hLP hLac

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08PC part (3) for the projection, existence.** The left derived functor of degreewise
lower shriek `π_!` on complexes of `π^{-1}O`-modules exists at every object. -/
instance hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy :
    (lowerShriekOnHomotopy (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (sourceQuasiIso (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O) :=
  (projectionSituation J).hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy O

/-- **The functor `Lπ_! : D(Δ × C, π^{-1}O) ⥤ D(O)` of Remark 09CY**: the unbounded left derived
functor of lower shriek `π_! : Mod(π^{-1}O) ⥤ Mod(O)` along the projection `π : Δ × C ⥤ C`, which
exists by Stacks 08PC part (3). -/
def derivedModuleLowerShriek :
    DerivedCategory (SheafOfModules.{u} (simplicialProjectionRing J O)) ⥤
      DerivedCategory (SheafOfModules.{u} O) :=
  Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek (simplicialProjectionTopology J) J
    (simplicialProjection (C := C)) O

/-- `Lπ_!` stays a left derived functor after composition with derived restriction, being
constructed by resolutions. -/
instance isLeftDerivedFunctor_derivedLowerShriek_comp_derivedRestriction :
    (Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek (simplicialProjectionTopology J) J
        (simplicialProjection (C := C)) O ⋙
      derivedRestriction (simplicialProjectionTopology J) J
          (simplicialProjection (C := C)) O).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
          (Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek
              (simplicialProjectionTopology J) J
            (simplicialProjection (C := C)) O)
          (derivedRestriction (simplicialProjectionTopology J) J
              (simplicialProjection (C := C)) O)).inv ≫
        Functor.whiskerRight
          (derivedLowerShriekComparison (simplicialProjectionTopology J) J
              (simplicialProjection (C := C)) O)
          (derivedRestriction (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O))
      (sourceQuasiIso (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic (simplicialProjectionTopology J) J _ O
    (lowerShriekModules_acyclic J O) _

/-- **Remark 09CY, `forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`**, for the projection `π : Δ × C ⥤ C`:
forgetting the module structure, derived lower shriek of `π^{-1}O`-modules is derived lower
shriek of abelian sheaves. This is Stacks 08PC part (4) for the projection
(`FibredCategorySituation.derivedForgetIso`). -/
def derivedModuleLowerShriekForgetIso :
    (SheafOfModules.toSheaf
        (simplicialProjectionRing J O)).mapDerivedCategory ⋙ derivedLowerShriek J ≅
      derivedModuleLowerShriek J O ⋙ (SheafOfModules.toSheaf O).mapDerivedCategory :=
  (projectionSituation J).derivedForgetIso O

/-- `π^{-1}` on derived categories of modules, induced by the exact functor `π^{-1}`. -/
abbrev derivedModuleInverseImage :
    DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} (simplicialProjectionRing J O)) :=
  derivedRestriction (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O

/-- **Stacks 08PC part (3) for the projection, adjunction**: `Lπ_! ⊣ π^{-1}` on derived
categories of modules. -/
def derivedModuleLowerShriekAdjunction :
    derivedModuleLowerShriek J O ⊣ derivedModuleInverseImage J O :=
  derivedLowerShriekAdjunction (simplicialProjectionTopology J) J (simplicialProjection (C := C)) O

/-- `Lπ_!` commutes with the shift, being left adjoint to `π^{-1}`, which does. -/
instance derivedModuleLowerShriek_commShift : (derivedModuleLowerShriek J O).CommShift ℤ :=
  (derivedModuleLowerShriekAdjunction J O).leftAdjointCommShift ℤ

/-- **`Lπ_!` is an exact functor of triangulated categories**: it is left adjoint to `π^{-1}`,
which is exact, being induced by an exact functor of abelian categories. -/
instance derivedModuleLowerShriek_isTriangulated : (derivedModuleLowerShriek J O).IsTriangulated :=
  have : (derivedModuleLowerShriekAdjunction J O).CommShift ℤ :=
    (derivedModuleLowerShriekAdjunction J O).commShift_of_rightAdjoint ℤ
  (derivedModuleLowerShriekAdjunction J O).isTriangulated_leftAdjoint

end Derived

end Stacks.SimplicialModules

end
