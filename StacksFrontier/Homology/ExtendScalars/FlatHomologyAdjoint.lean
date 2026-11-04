module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointSheafStalkCounitApply
public import StacksFrontier.Cotangent.BaseChangeComplexCounit

/-!
# Flat base change of cohomology along a semilinear map of complexes

Let `φ : S → S'` be a map of commutative rings, `L` a complex of `S`-modules, `L'` a complex of
`S'`-modules and `ψ : L ⟶ L'` a map of complexes linear over `φ`. On cohomology `ψ` induces an
`S`-linear map `H^i(L) ⟶ H^i(L')` and so an `S'`-linear map

`S' ⊗_S H^i(L) ⟶ H^i(L')`,  `s' ⊗ m ↦ s' · ψ(m)`.

When `φ` is flat, `S' ⊗_S -` is exact and commutes with cohomology, and this map is the
cohomology of the adjoint map of complexes `S' ⊗_S L ⟶ L'`; so it is an isomorphism as soon as
that adjoint map is a quasi-isomorphism. This is the algebra behind the étale localization of the
cohomology of cotangent complexes.

## Main definitions

* `ModuleCat.homologyRestrictScalarsMap`: the `S`-linear map `H^i(L) ⟶ H^i(L')` of `ψ`.
* `ModuleCat.homologyExtendScalarsAdjoint`: its adjoint `S' ⊗_S H^i(L) ⟶ H^i(L')`.

## Main results

* `ModuleCat.homologyExtendScalarsAdjoint_tmul`: it sends `s' ⊗ m` to `s' · ψ(m)`.
* `ModuleCat.homologyExtendScalarsAdjoint_eq`: for `φ` flat, it is the cohomology of the adjoint
  map of complexes.
* `ModuleCat.isIso_homologyExtendScalarsAdjoint`: for `φ` flat and the adjoint map of complexes a
  quasi-isomorphism, it is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace ModuleCat

variable {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
  {L : CochainComplex (ModuleCat.{u} S) ℤ} {L' : CochainComplex (ModuleCat.{u} S') ℤ}
  (ψ : L ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L')
  (i : ℤ) {M₀ : ModuleCat.{u} S}

/-- In `S ⊗_R M`, a scalar of `R` moves across the tensor through `φ`. -/
theorem extendScalars_mul_tmul (r : S) (s : S') (m : M₀) :
    (φ r * s) ⊗ₜ[S, φ] m = s ⊗ₜ[S, φ] (r • m) := by
  let := Module.compHom S' φ
  exact TensorProduct.smul_tmul r s m

/-- **The map on cohomology of a semilinear map of complexes**, `H^i(L) ⟶ H^i(L')` for a map
`ψ : L ⟶ L'` linear over `φ : S → S'`, as an `S`-linear map: the cohomology of `ψ`, followed by
the identification of the cohomology of the restriction of scalars of `L'` with the restriction of
scalars of its cohomology. -/
def homologyRestrictScalarsMap :
    L.homology i ⟶ (ModuleCat.restrictScalars φ).obj (L'.homology i) :=
  HomologicalComplex.homologyMap ψ i ≫
    (Stacks.Homology.exactHomologyIso (ModuleCat.restrictScalars φ) i).hom.app L'

/-- **The `S'`-linear adjoint of the map on cohomology of a semilinear map of complexes**,
`S' ⊗_S H^i(L) ⟶ H^i(L')`, `s' ⊗ m ↦ s' · m`. -/
def homologyExtendScalarsAdjoint :
    (ModuleCat.extendScalars φ).obj (L.homology i) ⟶ L'.homology i :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm (homologyRestrictScalarsMap φ ψ i)

/-- The adjoint map on cohomology sends `s' ⊗ m` to `s' · m`. -/
theorem homologyExtendScalarsAdjoint_tmul (s' : S') (m : L.homology i) :
    homologyExtendScalarsAdjoint φ ψ i (s' ⊗ₜ[S, φ] m) =
      s' • (homologyRestrictScalarsMap φ ψ i m : ToType (L'.homology i)) := by
  rw [homologyExtendScalarsAdjoint, Adjunction.homEquiv_counit]
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul φ _ s'
    (homologyRestrictScalarsMap φ ψ i m)

/-- On the class of a cocycle `z`, the map on cohomology is the class of the image of `z`. -/
theorem homologyRestrictScalarsMap_homologyπ (z : L.cycles i) :
    homologyRestrictScalarsMap φ ψ i (L.homologyπ i z) =
      (L'.homologyπ i (((L'.sc i).mapCyclesIso (ModuleCat.restrictScalars φ)).hom
        (HomologicalComplex.cyclesMap ψ i z)) : ToType (L'.homology i)) := by
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ψ i) z
  have h2 := ConcreteCategory.congr_hom
    (Stacks.Homology.exactHomologyIso_hom_app_homologyπ (ModuleCat.restrictScalars φ) i L')
    (HomologicalComplex.cyclesMap ψ i z)
  show (Stacks.Homology.exactHomologyIso (ModuleCat.restrictScalars φ) i).hom.app L'
      (HomologicalComplex.homologyMap ψ i (L.homologyπ i z)) = _
  rw [ConcreteCategory.comp_apply] at h1
  rwa [h1]

/-- **The adjoint map on cohomology is the cohomology of the adjoint map of complexes**, read
through the identification of the cohomology of `S' ⊗_S L` with `S' ⊗_S H^i(L)`, which holds for
`S → S'` flat. -/
theorem homologyExtendScalarsAdjoint_eq (hflat : φ.Flat) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    homologyExtendScalarsAdjoint φ ψ i =
      (Stacks.Homology.exactHomologyIso (ModuleCat.extendScalars φ) i).inv.app L ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
            ModuleCat.extendRestrictScalarsAdjCounitComplex φ (ComplexShape.up ℤ) L') i := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ i)).1 inferInstance m
  let E := ModuleCat.extendScalars φ
  let R := ModuleCat.restrictScalars.{u} φ
  let Φ := ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
    ModuleCat.extendRestrictScalarsAdjCounitComplex φ (ComplexShape.up ℤ) L'
  let one : S' := 1
  let w := ((L.sc i).mapCyclesIso E).inv (one ⊗ₜ[S, φ] z)
  have hl : homologyExtendScalarsAdjoint φ ψ i (one ⊗ₜ[S, φ] L.homologyπ i z) =
      L'.homologyπ i (((L'.sc i).mapCyclesIso R).hom (HomologicalComplex.cyclesMap ψ i z)) := by
    rw [homologyExtendScalarsAdjoint_tmul, one_smul]
    exact homologyRestrictScalarsMap_homologyπ φ ψ i z
  have hr0 : (Stacks.Homology.exactHomologyIso E i).inv.app L
      (E.map (L.homologyπ i) (one ⊗ₜ[S, φ] z)) =
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ i w :=
    ConcreteCategory.congr_hom
      (Stacks.Homology.map_homologyπ_exactHomologyIso_inv_app E i L) (one ⊗ₜ[S, φ] z)
  have hr1 : HomologicalComplex.homologyMap Φ i
      (((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ i w) =
        L'.homologyπ i (HomologicalComplex.cyclesMap Φ i w) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality Φ i) w
  have hc2 : ((L.sc i).map E).iCycles w = one ⊗ₜ[S, φ] (L.iCycles i z) := by
    have h := ConcreteCategory.congr_hom ((L.sc i).mapCyclesIso_hom_iCycles E) w
    have h' : ((L.sc i).mapCyclesIso E).hom w = one ⊗ₜ[S, φ] z :=
      Iso.inv_hom_id_apply ((L.sc i).mapCyclesIso E) _
    exact h.symm.trans (congrArg (E.map (L.sc i).iCycles) h')
  have hcyc : L'.iCycles i (HomologicalComplex.cyclesMap Φ i w) =
      L'.iCycles i (((L'.sc i).mapCyclesIso R).hom (HomologicalComplex.cyclesMap ψ i z)) := by
    have hc1 : L'.iCycles i (HomologicalComplex.cyclesMap Φ i w) =
        Φ.f i (((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).iCycles i w) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i Φ i) w
    have hc3 : R.map (L'.iCycles i)
        (((L'.sc i).mapCyclesIso R).hom (HomologicalComplex.cyclesMap ψ i z)) =
          ((L'.sc i).map R).iCycles (HomologicalComplex.cyclesMap ψ i z) :=
      ConcreteCategory.congr_hom ((L'.sc i).mapCyclesIso_hom_iCycles R)
        (HomologicalComplex.cyclesMap ψ i z)
    have hc4 : ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L').iCycles i
        (HomologicalComplex.cyclesMap ψ i z) = ψ.f i (L.iCycles i z) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ i) z
    have hc5 : Φ.f i (one ⊗ₜ[S, φ] (L.iCycles i z)) = ψ.f i (L.iCycles i z) :=
      ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ _ _
    exact hc1.trans ((congrArg (Φ.f i) hc2).trans (hc5.trans (hc4.symm.trans hc3.symm)))
  refine hl.trans ?_
  refine Eq.trans ?_ ((congrArg (HomologicalComplex.homologyMap Φ i) hr0).trans hr1).symm
  exact congrArg (L'.homologyπ i)
    ((ModuleCat.mono_iff_injective (L'.iCycles i)).1 inferInstance hcyc).symm

/-- **Flat base change of cohomology.** For a map of complexes `ψ : L ⟶ L'` linear over a flat
ring map `S → S'`, if the adjoint map `S' ⊗_S L ⟶ L'` is a quasi-isomorphism, then
`S' ⊗_S H^i(L) ⟶ H^i(L')`, `s' ⊗ m ↦ s' · m`, is an isomorphism. -/
theorem isIso_homologyExtendScalarsAdjoint (hflat : φ.Flat)
    (hq : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
      ModuleCat.extendRestrictScalarsAdjCounitComplex φ (ComplexShape.up ℤ) L')) :
    IsIso (homologyExtendScalarsAdjoint φ ψ i) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  rw [homologyExtendScalarsAdjoint_eq φ ψ i hflat]
  have : IsIso (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex φ (ComplexShape.up ℤ) L') i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 (hq.quasiIsoAt i)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (Iso.isIso_inv ((Stacks.Homology.exactHomologyIso (ModuleCat.extendScalars φ) i).app L)) this

end ModuleCat

end
