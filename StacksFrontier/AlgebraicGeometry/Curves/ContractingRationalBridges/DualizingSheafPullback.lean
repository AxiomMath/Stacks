module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Iterated
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PicardDescent
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroDegreeZero
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.DualizingPullbackPicard
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf along the contraction of a rational bridge

Let `k` be a field, `X` a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, `C ⊆ X` a rational bridge and `c : X ⟶ Y` its contraction
([Stacks, Tag 0E3M]). This file proves `c^* ω_Y ≅ ω_X` ([Stacks, Tag 0E3N]).

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_eq_finrank_mul_of_comp_SpecMap`: the degree of an
  invertible module on a curve over `k'` is `[k' : k]` times its degree over `k'`.
* `AlgebraicGeometry.nonempty_pullback_dualizingSheafOverField_iso_unit_of_isRationalBridge`:
  `ω_X|_C ≅ 𝒪_C` on a rational bridge.
* `Stacks.Curves.isProper_structureMorphism_of_isContractionOfRationalBridge`: the structure
  morphism of the target of the contraction is proper.
* `Stacks.Curves.nonempty_pullback_dualizingSheafOverField_iso_contraction_bridge`:
  `c^* ω_Y ≅ ω_X`.

## References

* [Stacks Project, Tag 0E3N](https://stacks.math.columbia.edu/tag/0E3N)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0C6M](https://stacks.math.columbia.edu/tag/0C6M)
* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Let `Y` be proper of dimension at most one over a field `k'` and view it over a subfield
`k ⊆ k'`. For an invertible `𝒪_Y`-module `ℒ`, `deg_k ℒ = [k' : k] · deg_{k'} ℒ`. -/
theorem invertibleCurveDegree_eq_finrank_mul_of_comp_SpecMap (k k' : Type u) [Field k]
    [Field k'] [Algebra k k'] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f]
    (f' : Y ⟶ Spec (.of k')) [IsProper f']
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = f)
    (hdim : topologicalKrullDim Y ≤ 1) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L =
      (Module.finrank k k' : ℤ) * invertibleCurveDegree k' f' hdim L := by
  subst hf
  rw [invertibleCurveDegree_eq_sub_of_isZero k _ hdim L
      (isZero_cohomologyOverField_two_le k _ hdim L) (isZero_cohomologyOverField_two_le k _ hdim _),
    invertibleCurveDegree_eq_sub_of_isZero k' f' hdim L
      (isZero_cohomologyOverField_two_le k' f' hdim L)
      (isZero_cohomologyOverField_two_le k' f' hdim _)]
  simp only [finrank_cohomologyOverField_comp_SpecMap k k' f' L,
    finrank_cohomologyOverField_comp_SpecMap k k' f' (SheafOfModules.unit Y.ringCatSheaf)]
  push_cast
  ring

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Let `X` be a proper scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. Then `ω_X|_C ≅ 𝒪_C`. -/
theorem nonempty_pullback_dualizingSheafOverField_iso_unit_of_isRationalBridge
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    Nonempty ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) ≅
      SheafOfModules.unit C.subscheme.ringCatSheaf) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
  have hdeg :=
    invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hdim
      hnodal C hC
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  let : Algebra k Γ(C.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(C.subscheme, ⊤))).inv ≫ C.subscheme.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hf : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.subscheme, ⊤))) =
      fC := by
    show C.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop) = fC
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have : Module.Finite k Γ(C.subscheme, ⊤) := (isField_and_finite_globalSections k fC).2
  have : IsCurve Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ :=
    { topologicalKrullDim_eq_one := hCdim }
  have hdeg' : invertibleCurveDegree Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ hCdim.le
      ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0 := by
    have h : (Module.finrank k Γ(C.subscheme, ⊤) : ℤ) *
        invertibleCurveDegree Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ hCdim.le
          ((Scheme.Modules.pullback C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0 :=
      (invertibleCurveDegree_eq_finrank_mul_of_comp_SpecMap k Γ(C.subscheme, ⊤) fC
        C.subscheme.toSpecΓ hf hCdim.le _).symm.trans hdeg
    have hpos : (0 : ℤ) < Module.finrank k Γ(C.subscheme, ⊤) := mod_cast Module.finrank_pos
    exact (mul_eq_zero.1 h).resolve_left hpos.ne'
  exact isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ _ hC.genus_eq_zero hdeg'

end AlgebraicGeometry

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- Let `c : X ⟶ Y` be the contraction of a rational bridge. Any morphism `g : Y ⟶ Spec k` with
`c ≫ g` the structure morphism of `X` is proper. -/
theorem isProper_structureMorphism_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {g : Y ⟶ Spec (.of k)}
    (hcg : c ≫ g = X ↘ Spec (.of k)) : IsProper g := by
  obtain ⟨g', hcg', hg', -⟩ :=
    exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim hnodal C hC c hc
  rwa [← structureMorphism_eq_of_isContractionOfRationalBridge hdim hnodal hc
    (hcg'.trans hcg.symm)]

/-- Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge and let
`c : X ⟶ Y` be the contraction of `C`, with `Y` over `k` through `g`, compatibly with `c`. Then
`c^* ω_Y ≅ ω_X`. -/
@[stacks 0E3N]
theorem nonempty_pullback_dualizingSheafOverField_iso_contraction_bridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (g : Y ⟶ Spec (.of k))
    (hcg : c ≫ g = X ↘ Spec (.of k)) :
    haveI := isProper_structureMorphism_of_isContractionOfRationalBridge hdim hnodal hc hcg
    Nonempty ((Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField g) ≅
      Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) := by
  obtain ⟨g', hcg', hg', hdimY, hΓY, -⟩ :=
    exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim hnodal C hC c hc
  obtain rfl : g' = g :=
    structureMorphism_eq_of_isContractionOfRationalBridge hdim hnodal hc (hcg'.trans hcg.symm)
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have hωX := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have hYnodal := hasAtWorstNodalSingularities_of_isContractionOfRationalBridge hdim hnodal hc hcg'
  let : Y.Over (Spec (.of k)) := ⟨g'⟩
  have : IsProper (Y ↘ Spec (.of k)) := hg'
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) := hΓY
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  have hωY := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdimY
    hYnodal
  have : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField g') :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hωY
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Duality.dualizingSheafOverField g') 1 :=
    Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule _
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hωX
  obtain ⟨eC⟩ := nonempty_pullback_dualizingSheafOverField_iso_unit_of_isRationalBridge hdim
    hnodal C hC
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    exists_pullback_iso_of_pullback_subschemeι_iso_unit_contraction_bridge hdim hnodal hc _ eC
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
    Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule N
  have : IsProper (c ≫ g') := by rw [hcg']; infer_instance
  have hω : Stacks.Duality.dualizingSheafOverField (c ≫ g') =
      Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)) := by
    have key : ∀ (f₁ f₂ : X ⟶ Spec (.of k)) [IsProper f₁] [IsProper f₂], f₁ = f₂ →
        Stacks.Duality.dualizingSheafOverField f₁ = Stacks.Duality.dualizingSheafOverField f₂ := by
      rintro f₁ f₂ _ _ rfl
      rfl
    exact key _ _ hcg'
  obtain ⟨e'⟩ := Stacks.Curves.DualizingPullback.nonempty_pullback_iso_of_pullback_iso c g'
    hdim.le hdimY.le (isIso_structureSheafToPushforward_contraction_bridge hdim hnodal hc)
    (rightAcyclic_pushforward_ambientStructureSheaf_bridge hdim hnodal hc 1 one_pos) N
    (e ≪≫ eqToIso hω.symm)
  exact ⟨e' ≪≫ eqToIso hω⟩

end Stacks.Curves

end
