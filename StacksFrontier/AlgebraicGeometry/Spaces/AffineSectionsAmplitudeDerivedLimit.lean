module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.Bound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Affine amplitude of objects with quasi-coherent cohomology and of their derived limits

Let `X` be an algebraic space and `I` a K-injective complex of `𝒪_X`-modules on the small étale
site. The complexes of sections `Γ(V, I)` over the affine étale charts `V` compute the
hypercohomology `H^i(V, I)`.

* If `I` has quasi-coherent cohomology sheaves vanishing above `a`, then `Γ(V, I)` has no
  cohomology above `a` (`AlgebraicGeometry.Space.sectionsAmplitudeLE_of_vanishesAbove`): this is
  the upper bound of Stacks 08F7 at `N = 1`, a quasi-coherent module having no higher cohomology
  on an affine étale chart.
* If `I` represents a derived limit `R lim Eₙ` of objects with quasi-coherent cohomology vanishing
  above `a`, then `Γ(V, I)` has no cohomology above `a + 1`
  (`AlgebraicGeometry.Space.sectionsAmplitudeLE_of_isDerivedLimit`): derived sections over `V`
  carry the derived limit to a derived limit (Stacks 08U1), and a derived limit of objects in
  degrees `≤ a` lies in degrees `≤ a + 1` (the Milnor sequence, Stacks 0D60, costs one degree).

This is the reduction in the proof of Stacks 0DIL from the boundedness of `R lim Kₙ` to a uniform
upper bound on the `Kₙ`, in the form consumed by the bound of the coherator,
`AlgebraicGeometry.Space.SectionsAmplitudeLE`.

## Implementation notes

The derived categories are those of `AlgebraicGeometry.Space.spaceDerivedCategory`, the standard
model, which the inputs (Stacks 08F7 and 08U1 as stated in this library) are written at; it is
taken by proof-local `letI`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The abelian-group-valued sections over an étale chart preserve countable products. -/
instance preservesLimitsOfShape_sectionsFunctor (V : SmallEtale B S hS X.1) :
    PreservesLimitsOfShape (Discrete ℕ) (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS X.1 X.2) V) := by
  dsimp [Stacks.Cohomology.SiteInverseLimits.sectionsFunctor]
  infer_instance

/-- If the derived sections functor over an affine étale chart `V` carries `K ≅ Q I` into degrees
`≤ c`, for `I` K-injective, then `Γ(V, I)` has no cohomology above `c`. -/
private theorem isZero_sectionsComplex_homology_of_isLE
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)] [HasDerivedCategory AddCommGrpCat.{u}]
    [EnoughInjectives (Modules.{u, u} B S hS X.1 X.2)]
    [IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2)]
    (V : SmallEtale B S hS X.1) (hV : IsAffineChart B S hS X.1 V)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (e : DerivedCategory.Q.obj I ≅ K)
    (c : ℤ)
    (hc : ∀ (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory AddCommGrpCat.{u})
      (α : (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS X.1 X.2) V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
      [RF.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))],
      (∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite → ∀ p : ℤ, ((1 : ℕ) : ℤ) ≤ p →
        IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS X.1 X.2) V).rightDerivedPlus p).obj M)) →
      (RF.obj K).IsLE c)
    (i : ℤ) (hi : c < i) :
    IsZero (((sectionsComplex B S hS X V).obj I).homology i) := by
  let F :=
    Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X.1 X.2) V
  have hkey :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)
  have := hkey.1
  have : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  let RF := (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  let α := (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  have := hc RF α fun M hM p hp ↦ by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _
      (rfl : ((n : ℕ) : ℤ) = ((n : ℕ) : ℤ)) M).2
      (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS X.1 X.2 M hM V hV n (by omega))
  refine IsZero.of_iso (DerivedCategory.isZero_of_isLE (RF.obj K) c i hi)
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso ?_)
  refine ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫ ?_
  refine (@asIso _ _ _ _ _ (hkey.2 DerivedCategory.Qh RF α I hI)) ≪≫ ?_
  exact RF.mapIso ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X.1 X.2)).app I ≪≫ e)

/-- **Affine amplitude of an object with quasi-coherent cohomology.** If the cohomology sheaves of
a K-injective complex `I` are quasi-coherent and vanish above `a`, then its complexes of sections
over the affine étale charts have no cohomology above `a`. -/
theorem sectionsAmplitudeLE_of_vanishesAbove (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective)
    (hqc : ∀ q : ℤ, ((spaceDerivedHomology B S hS X q).obj
      ((spaceDerivedQ B S hS X).obj I)).IsQuasicoherentOnSite)
    (a : ℤ) (ha : SpaceCohomologyVanishesAbove B S hS X a ((spaceDerivedQ B S hS X).obj I)) :
    SectionsAmplitudeLE B S hS X a I := by
  -- The standard model, at which Stacks 08F7 is stated here.
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have := hasProductsOfShape_nat_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  intro V hV i hi
  refine isZero_sectionsComplex_homology_of_isLE B S hS X V hV I hI _ (Iso.refl _)
    (a + (1 : ℕ) - 1) ?_ i (by omega)
  intro RF α _ hvan
  exact isLE_rightDerived_obj_of_isLE B S hS X.1 X.2 _ RF α 1 hvan _ hqc a
    ((DerivedCategory.isLE_iff _ a).2 ha)

/-- **Affine amplitude of a derived limit (the Milnor step of Stacks 0DIL).** Let `(Eₙ)` be an
inverse system in `D(𝒪_X)` whose terms have quasi-coherent cohomology sheaves vanishing above `a`,
and let `I` be a K-injective complex representing a derived limit of it. Then the complexes of
sections of `I` over the affine étale charts have no cohomology above `a + 1`. -/
theorem sectionsAmplitudeLE_of_isDerivedLimit (L : ℕᵒᵖ ⥤ spaceDerivedCategory B S hS X)
    [HasProduct fun n : ℕ ↦ L.obj ⟨n⟩] (K : spaceDerivedCategory B S hS X)
    (p : K ⟶ ∏ᶜ fun n : ℕ ↦ L.obj ⟨n⟩)
    (hK : ∃ δ : (∏ᶜ fun n : ℕ ↦ L.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ L.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ L.obj ⟨n⟩) (n + 1) ≫ L.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory B S hS X))
    (a : ℤ)
    (hqc : ∀ (n : ℕ) (q : ℤ), ((spaceDerivedHomology B S hS X q).obj
      (L.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hL : ∀ n : ℕ, SpaceCohomologyVanishesAbove B S hS X a (L.obj ⟨n⟩))
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective)
    (e : (spaceDerivedQ B S hS X).obj I ≅ K) :
    SectionsAmplitudeLE B S hS X (a + 1) I := by
  -- The standard model, at which Stacks 08F7 and 08U1 are stated here.
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have := hasProductsOfShape_nat_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have : HasProductsOfShape ℕ (DerivedCategory AddCommGrpCat.{u}) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  intro V hV i hi
  refine isZero_sectionsComplex_homology_of_isLE B S hS X V hV I hI K e (a + 1) ?_ i hi
  intro RF α _ hvan
  have hterm : ∀ n : ℕ, ((L ⋙ RF).obj ⟨n⟩).IsLE a := fun n ↦ by
    simpa using isLE_rightDerived_obj_of_isLE B S hS X.1 X.2 _ RF α 1 hvan (L.obj ⟨n⟩) (hqc n) a
      ((DerivedCategory.isLE_iff _ a).2 (hL n))
  obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor _ RF α L K p hK
  exact Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit (L ⋙ RF) (RF.obj K) ⟨_, δ, hδ⟩ a hterm

end AlgebraicGeometry.Space

end
