module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.Cotangent.Spaces.CotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# Cohomology sheaves of an object of `D(𝒪_X)` tested on derived stalks

Let `X` be an algebraic space over a scheme `S` and let `E` be an object of the derived category
of `𝒪_X`-modules on the small étale site, with sections in the universe of the site, the category
in which the cotangent complex of a morphism out of `X` lives
(`AlgebraicGeometry.Space.smallEtaleModulesULift`). At a geometric point `x̄` of `X` the stalk
functor is exact, so it induces the derived stalk `E ↦ E_x̄` on derived categories
(`Stacks.derivedModuleFiber`), which commutes with taking cohomology. Since the geometric points
form a conservative family of points of the small étale site
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint`), a cohomology sheaf
of `E` vanishes as soon as the corresponding cohomology of every derived stalk does.

This is the form in which the proof of [Stacks, Tag 09DM] reads the vanishing `H^0(E) = H^{-1}(E)
= 0` of the object of Equation 92.28.0.1 off its stalks, and the identification of
`H^{-2}(E)_{x̄}` with `H^{-2}` of the derived stalk.

## Main definitions

* `AlgebraicGeometry.Space.derivedStalk`: the derived stalk at a geometric point.
* `AlgebraicGeometry.Space.homologyDerivedStalkIso`: `H^i(E)_{x̄} ≅ H^i(E_{x̄})`.

## Main results

* `Stacks.isZero_homology_of_forall_isZero_homology_derivedModuleFiber`: on any site, a
  cohomology sheaf vanishes when the corresponding cohomology of every derived stalk at one
  conservative family of points vanishes.
* `AlgebraicGeometry.Space.isZero_homology_of_forall_derivedStalk`: the same on the small étale
  site of an algebraic space, at its geometric points.

## References

* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u d e

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (commRingSheafToRingSheaf O))]

/-- **Cohomology sheaves are tested on derived stalks.** If, at every member of a conservative
family of points of the site, the `i`-th cohomology of the derived stalk of `E` vanishes, then
the `i`-th cohomology sheaf of `E` vanishes: its stalk at each such point is that cohomology, the
stalk functor being exact (part (1) of Stacks 04EQ). -/
theorem isZero_homology_of_forall_isZero_homology_derivedModuleFiber
    (E : DerivedCategory (SheafOfModules.{w} (commRingSheafToRingSheaf O)))
    {t : Type*} (p : t → J.Point.{w}) (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (i : ℤ)
    [∀ k, HasDerivedCategory.{e}
      (ModuleCat.{w} (((p k).presheafFiber (A := CommRingCat.{w})).obj O.obj))]
    (h : ∀ k, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{w} (((p k).presheafFiber (A := CommRingCat.{w})).obj O.obj)) i).obj
        ((derivedModuleFiber (p k) O).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (commRingSheafToRingSheaf O)) i).obj E) := by
  refine isZero_of_forall_isZero_sheafModuleFiber _ hp (fun ⟨Φ, hΦ⟩ => ?_)
  obtain ⟨k, rfl⟩ := (ObjectProperty.ofObj_iff p Φ).1 hΦ
  have hstalk : IsZero ((sheafModuleFiberOfCommRing (p k) O).obj
      ((DerivedCategory.homologyFunctor _ i).obj E)) :=
    (h k).of_iso (((sheafModuleFiberOfCommRing (p k) O).mapDerivedCategoryHomologyIso i).app E).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hstalk ⊢
  exact hstalk

end Stacks

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)

/-- The point of the small étale site of `W`, with fibres in the universe of the coefficients,
attached to a geometric point `x̄` of `W`. -/
abbrev geometricSitePoint (x : GeometricPoint B S hS W.1) :
    (smallEtaleRingedTopos B S hS W).J.Point.{u + 1} :=
  (etaleSitePoint B S hS W.1 x W.2).ulift.{u + 1}

/-- **The derived stalk at a geometric point.** The functor `D(𝒪_W) ⥤ D(𝒪_{W, x̄})`, `E ↦ E_x̄`,
induced by the exact stalk functor at the geometric point `x̄`; the ring is the stalk of the lifted
structure sheaf, which is the étale local ring by
`AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv`. -/
noncomputable abbrev derivedStalk (x : GeometricPoint B S hS W.1) :
    DerivedCategory (smallEtaleModulesULift B S hS W) ⥤
      DerivedCategory (ModuleCat.{u + 1} (((geometricSitePoint B S hS W x).presheafFiber
        (A := CommRingCat.{u + 1})).obj (smallEtaleStructureSheafULift B S hS W).obj)) :=
  Stacks.derivedModuleFiber (geometricSitePoint B S hS W x) (smallEtaleStructureSheafULift B S hS W)

/-- **The stalk of a cohomology sheaf is the cohomology of the derived stalk**:
`H^i(E)_x̄ ≅ H^i(E_x̄)`, the stalk functor being exact. -/
noncomputable def homologyDerivedStalkIso (x : GeometricPoint B S hS W.1)
    (E : DerivedCategory (smallEtaleModulesULift B S hS W)) (i : ℤ) :
    (Stacks.sheafModuleFiberOfCommRing (geometricSitePoint B S hS W x)
        (smallEtaleStructureSheafULift B S hS W)).obj
        ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) i).obj E) ≅
      (DerivedCategory.homologyFunctor _ i).obj ((derivedStalk B S hS W x).obj E) :=
  (((Stacks.sheafModuleFiberOfCommRing (geometricSitePoint B S hS W x)
    (smallEtaleStructureSheafULift B S hS W)).mapDerivedCategoryHomologyIso i).app E).symm

/-- **A cohomology sheaf of an object of `D(𝒪_W)` vanishes when it vanishes on derived stalks at
the geometric points.** -/
theorem isZero_homology_of_forall_derivedStalk
    (E : DerivedCategory (smallEtaleModulesULift B S hS W)) (i : ℤ)
    (h : ∀ x : GeometricPoint B S hS W.1,
      IsZero ((DerivedCategory.homologyFunctor _ i).obj ((derivedStalk B S hS W x).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) i).obj E) :=
  Stacks.isZero_homology_of_forall_isZero_homology_derivedModuleFiber
    (smallEtaleStructureSheafULift B S hS W) E (geometricSitePoint B S hS W)
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS W.1 W.2) i h

end AlgebraicGeometry.Space

end
