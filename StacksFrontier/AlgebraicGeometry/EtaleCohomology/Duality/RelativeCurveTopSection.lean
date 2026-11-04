module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalEdgeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSectionsCanonical
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# A generating section of `R² f_* μ_n` for a smooth proper family of curves

Let `f : X ⟶ S` be proper, smooth of relative dimension one, with geometrically irreducible
fibres, and `n` invertible on `X`. Write `G = H⁰(Rf_*(μ_n[2])) = R² f_* μ_n`. By proper base
change along `f` itself (Tag 0DDE) the edge map of the Kummer class of the diagonal
(`Stacks.EtaleCohomology.diagonalEdge`) is a morphism `σ : ℤ_X ⟶ f⁻¹ G`
(`Stacks.EtaleCohomology.relativeTopEdge`), which at every geometric point `x̄` of `X` with
algebraically closed residue field is a generator of order `n`
(`Stacks.EtaleCohomology.isZModGenerator_relativeTopEdge`). Since `f` is flat, quasi-compact and
geometrically connected, global sections do not change under `f⁻¹` (Tag 0A3H), so `σ` descends:
`σ = f⁻¹ τ` for a section `τ : ℤ_S ⟶ G` (`Stacks.EtaleCohomology.exists_relativeTopSection`).

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which the
base change map of Tag 0A2A is stated.

## Main definitions

* `Stacks.EtaleCohomology.relativeTopSheaf`: `G = H⁰(Rf_*(μ_n[2]))`.
* `Stacks.EtaleCohomology.relativeTopBaseChangeIso`: `f⁻¹Rf_*(μ_n[2]) ≅ Rpr₂_*(μ_n[2])`.
* `Stacks.EtaleCohomology.relativeTopEdge`: `σ : ℤ_X ⟶ f⁻¹ G`.

## Main results

* `Stacks.EtaleCohomology.isZModGenerator_relativeTopEdge`.
* `Stacks.EtaleCohomology.exists_relativeTopSection`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {S X : Scheme.{u}} (f : X ⟶ S) {n : ℕ}

/-- `R² f_* μ_n`, read as `H⁰(Rf_*(μ_n[2]))`. -/
abbrev relativeTopSheaf (n : ℕ) : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor _ 0).obj ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
    (((DerivedCategory.singleFunctor _ 0).obj
      (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n))⟦(2 : ℤ)⟧))

/-- The inverse image of `μ_n[2]` along `pr₁ : X ×_S X ⟶ X` is `μ_n[2]`. -/
def inverseImageShiftSingleRootsOfUnityIso {Y : Scheme.{u}} (g : Y ⟶ X)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) :
    (etaleAbelianDerivedInverseImage.{u, 0} g).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n))⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y n))⟦(2 : ℤ)⟧ :=
  ((etaleAbelianDerivedInverseImage.{u, 0} g).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (Stacks.Kummer.rootsOfUnityInverseImageIso.{u, u + 1} g n hX))

variable [IsProper f]

/-- **Proper base change along `f` itself**: `f⁻¹Rf_*(μ_n[2]) ≅ Rpr₂_*(μ_n[2])` for the cartesian
square `pr₁ ≫ f = pr₂ ≫ f` of `X ×_S X` (Tag 0DDE). -/
def relativeTopBaseChangeIso (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) :
    (etaleAbelianDerivedInverseImage.{u, 0} f).obj ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n))⟦(2 : ℤ)⟧)) ≅
      (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧) :=
  haveI := isIso_etaleAbelianDerivedBaseChange_of_isProper f (IsPullback.of_hasPullback f f)
    (((DerivedCategory.singleFunctor _ 0).obj
      (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n))⟦(2 : ℤ)⟧)
    (-2) (DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega))
    (torsionCohomologyProperty_shift_single_rootsOfUnity _ hn0)
  asIso ((etaleAbelianDerivedBaseChange.{u, 0} f f (pullback.fst f f) (pullback.snd f f)
      (IsPullback.of_hasPullback f f).w).app _) ≪≫
    (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).mapIso
      (inverseImageShiftSingleRootsOfUnityIso (pullback.fst f f) hX)

variable [SmoothOfRelativeDimension 1 f]

/-- **The edge map of the Kummer class of the diagonal, as a morphism of sheaves**
`σ : ℤ_X ⟶ f⁻¹(R² f_* μ_n)`. -/
def relativeTopEdge (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤))) :
    intSheaf X ⟶ (etaleAbelianInverseImage.{u, 0} f).obj (relativeTopSheaf f n) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (intSheaf X)).inv ≫
    (DerivedCategory.homologyFunctor _ 0).map
      (diagonalEdge f hn0 hY ≫ (relativeTopBaseChangeIso f hn0 hX).inv) ≫
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
      (etaleAbelianInverseImage.{u, 0} f) 0).app _).hom

section Generator

variable [GeometricallyIrreducible f] (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤)))

include hn0 hX hY in
/-- **`σ` generates at every geometric point.** For `x̄ : Spec Ω ⟶ X`, `Ω` algebraically closed,
the restriction `ℤ_Ω ⟶ x̄⁻¹f⁻¹(R² f_* μ_n)` of `σ` is a generator of order `n` of the group of
such morphisms. -/
theorem isZModGenerator_relativeTopEdge {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (hn : IsUnit (n : Ω)) :
    IsZModGenerator n
      (((etaleAbelianInverseImageConstantIso.{u, 0} x).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, 0} x).map (relativeTopEdge f hn0 hX hY)) := by
  set ψ := diagonalEdge f hn0 hY ≫ (relativeTopBaseChangeIso f hn0 hX).inv with hψ
  have h1 : IsZModGenerator n ((DerivedCategory.homologyFunctor _ 0).map
      ((etaleAbelianDerivedInverseImage.{u, 0} x).map ψ)) := by
    have := (isZModGenerator_homologyMap_diagonalEdge f hn0 hY x hn).map
      (isoHomAddEquiv (Iso.refl _) ((DerivedCategory.homologyFunctor _ 0).mapIso
        ((etaleAbelianDerivedInverseImage.{u, 0} x).mapIso
          (relativeTopBaseChangeIso f hn0 hX).symm)))
    simpa [isoHomAddEquiv, hψ] using this
  have hE : relativeTopEdge f hn0 hX hY =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (intSheaf X)).inv ≫
        (DerivedCategory.homologyFunctor _ 0).map ψ ≫
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
          (etaleAbelianInverseImage.{u, 0} f) 0).app _).hom := by
    rw [hψ]
    rfl
  clear_value ψ
  let ν := StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (etaleAbelianInverseImage.{u, 0} x) 0
  let I₁ :=
    ((etaleAbelianInverseImageConstantIso.{u, 0} x).app (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
      (etaleAbelianInverseImage.{u, 0} x).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (intSheaf X)).symm ≪≫
      (ν.app ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X))).symm
  let I₂ := ν.app ((etaleAbelianDerivedInverseImage.{u, 0} f).obj
      ((etaleAbelianDerivedDirectImage.{u, 0} f).obj (((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n))⟦(2 : ℤ)⟧))) ≪≫
    (etaleAbelianInverseImage.{u, 0} x).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
        (etaleAbelianInverseImage.{u, 0} f) 0).app _)
  have key : ((etaleAbelianInverseImageConstantIso.{u, 0} x).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
      (etaleAbelianInverseImage.{u, 0} x).map (relativeTopEdge f hn0 hX hY) =
      I₁.hom ≫ (DerivedCategory.homologyFunctor _ 0).map
        ((etaleAbelianDerivedInverseImage.{u, 0} x).map ψ) ≫ I₂.hom := by
    simp only [I₁, I₂, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      Category.assoc, hE, Functor.map_comp]
    rw [reassoc_of% (ν.hom.naturality ψ), Iso.inv_hom_id_app_assoc]
  rw [key]
  exact h1.map (isoHomAddEquiv I₁ I₂)

include hn0 hX hY in
/-- **`σ` descends to `S`** (Tag 0A3H): `f` is flat, quasi-compact and geometrically connected, so
`H⁰(S, G) → H⁰(X, f⁻¹G)` is bijective, and `σ = f⁻¹τ` for a section `τ : ℤ_S ⟶ G`. -/
theorem exists_relativeTopSection :
    ∃ τ : intSheaf S ⟶ relativeTopSheaf f n,
      ((etaleAbelianInverseImageConstantIso.{u, 0} f).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, 0} f).map τ = relativeTopEdge f hn0 hX hY := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GeometricallyConnected f := by
    rw [GeometricallyConnected.eq_geometrically]
    intro K _ y Z fst snd hpull
    have : IrreducibleSpace Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd hpull
    exact connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ Z).isConnected
  have := isIso_globalSectionsSmallEtaleInverseImage_of_flat_quasiCompact.{u, 0} f
  obtain ⟨z, hz⟩ := (etaleCohomologyRestrictionMap_zero_bijective_of_isIso.{u, u + 1} f
    (relativeTopSheaf f n)).2 (Abelian.Ext.mk₀ (relativeTopEdge f hn0 hX hY))
  obtain ⟨τ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 z
  refine ⟨τ, (Abelian.Ext.mk₀_bijective _ _).1 ?_⟩
  rwa [etaleCohomologyRestrictionMap_apply, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀] at hz

end Generator

end Stacks.EtaleCohomology

end
