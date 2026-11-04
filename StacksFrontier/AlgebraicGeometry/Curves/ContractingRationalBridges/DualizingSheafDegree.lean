module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChangeUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree

/-!
# The degree of the dualizing sheaf on a rational bridge

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. The exact sequence
`0 ⟶ ω_C ⟶ ω_X|_C ⟶ 𝒪_{C ∩ X'} ⟶ 0` of [Stacks, Tag 0E34] gives
`deg(ω_X|_C) = deg(C ∩ X') - 2 χ(C, 𝒪_C) = 2[k' : k] - 2[k' : k] = 0`.

## Main results

* `invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge`:
  `deg(ω_X|_C) = 0` on a rational bridge `C`.

## References

* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0E34](https://stacks.math.columbia.edu/tag/0E34)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. Then `deg(ω_X|_C) = 0`, where
`ω_X` is invertible by `isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities`. -/
@[stacks 0E64]
theorem invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
      hnodal
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
    invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC).le
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0 := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal
  let f := X ↘ Spec (.of k)
  let fC := C.subschemeι ≫ f
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  have hXeq : Equidimensional X := equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have hCeq : Equidimensional C.subscheme := Equidimensional.of_preirreducibleSpace C.subscheme
  obtain ⟨a, b, w, hS⟩ := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible
    f hXeq hdim C hCeq hCdim).2.2.2.2.2.2.2.2.1
  let : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι _ hω
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
  let : C.subscheme.Over (Spec (.of k)) := ⟨fC⟩
  have : LocallyOfFiniteType (C.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType fC)
  have : IsGorenstein C.subscheme :=
    Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k C.subscheme hCeq hCdim
      (Stacks.Curves.hasAtWorstNodalSingularities_subscheme hXeq hdim hnodal C hCeq hCdim)
  have := isInvertible_dualizingSheafOverField_of_connectedSpace Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ hCdim
  exact invertibleCurveDegree_eq_zero_of_isRationalBridge hdim hC _ Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ hf hS (Iso.refl _) (Iso.refl _)

end AlgebraicGeometry

end
