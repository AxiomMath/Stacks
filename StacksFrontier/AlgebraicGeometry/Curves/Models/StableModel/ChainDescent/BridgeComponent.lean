module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafPullback
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound

/-!
# A rational bridge as a one-dimensional component, and degree-zero modules on it

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, and let
`C ⊆ X` be a rational bridge ([Stacks, Tag 0E3M]). Being integral and one-dimensional, `C` is the
reduced component of `X` at its generic point: its generic point lies in
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X`, and `C` is isomorphic over `X` to
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ`. An invertible `𝒪_X`-module whose
restriction to that component has degree zero over `k` is trivial on `C`: the degree over `k` is
`[k' : k]` times the degree over the field `k' = H⁰(C, 𝒪_C)`, over which `C` is a proper curve of
genus zero with `H⁰(C, 𝒪_C) = k'`, so [Stacks, Tag 0C6M] applies. This is the argument of
`AlgebraicGeometry.nonempty_pullback_dualizingSheafOverField_iso_unit_of_isRationalBridge`, for an
arbitrary invertible module of degree zero.

## Main results

* `Stacks.Curves.exists_genericPointsOne_reducedComponent_iso_of_isRationalBridge`.
* `Stacks.Curves.nonempty_pullback_subschemeι_iso_unit_of_isRationalBridge`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A rational bridge is a one-dimensional component.** The generic point `ζ` of a rational
bridge `C` indexes a one-dimensional irreducible component of `X`, with closure the support of
`C`, and `C` is isomorphic over `X` to the reduced component at `ζ`. -/
theorem exists_genericPointsOne_reducedComponent_iso_of_isRationalBridge
    (hdim : topologicalKrullDim X = 1) {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∃ ζ : genericPointsOne X, closure ({ζ.1} : Set X) = (C.support : Set X) ∧
      ∃ ψ : C.subscheme ⟶ reducedComponent X ζ, IsIso ψ ∧
        ψ ≫ reducedComponentι X ζ = C.subschemeι := by
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim := topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  let ζ : genericPointsOne X :=
    ⟨_, genericPoint_mem_genericPointsOne C.subschemeι hdim.le hCdim⟩
  refine ⟨ζ, ?_, exists_isIso_hom_to_reducedComponent C.subschemeι ζ rfl⟩
  simpa using (support_ker_eq_closure_genericPoint C.subschemeι).symm

/-- **An invertible module of degree zero on a rational bridge is trivial there.** If the
restriction of an invertible `𝒪_X`-module `L` to the rational bridge `C` has degree zero over `k`,
then `L|_C ≅ 𝒪_C` ([Stacks, Tag 0C6M] over the field `H⁰(C, 𝒪_C)`). -/
theorem nonempty_pullback_subschemeι_iso_unit_of_isRationalBridge
    (hdim : topologicalKrullDim X = 1) (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : haveI := SheafOfModules.isInvertible_pullback C.subschemeι L
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC).le
        ((Scheme.Modules.pullback C.subschemeι).obj L) = 0) :
    Nonempty ((Scheme.Modules.pullback C.subschemeι).obj L ≅
      SheafOfModules.unit C.subscheme.ringCatSheaf) := by
  have := SheafOfModules.isInvertible_pullback C.subschemeι L
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  let : Algebra k Γ(C.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(C.subscheme, ⊤))).inv ≫ C.subscheme.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hf : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.subscheme, ⊤))) =
      fC := by
    change C.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop) = fC
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have : Module.Finite k Γ(C.subscheme, ⊤) := (isField_and_finite_globalSections k fC).2
  have : IsCurve Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ :=
    { topologicalKrullDim_eq_one := hCdim }
  have hdeg' : invertibleCurveDegree Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ hCdim.le
      ((Scheme.Modules.pullback C.subschemeι).obj L) = 0 := by
    have h : (Module.finrank k Γ(C.subscheme, ⊤) : ℤ) *
        invertibleCurveDegree Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ hCdim.le
          ((Scheme.Modules.pullback C.subschemeι).obj L) = 0 :=
      (invertibleCurveDegree_eq_finrank_mul_of_comp_SpecMap k Γ(C.subscheme, ⊤) fC
        C.subscheme.toSpecΓ hf hCdim.le _).symm.trans hdeg
    have hpos : (0 : ℤ) < Module.finrank k Γ(C.subscheme, ⊤) := by
      exact_mod_cast Module.finrank_pos
    exact (mul_eq_zero.1 h).resolve_left hpos.ne'
  exact isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ _ hC.genus_eq_zero hdeg'

end Stacks.Curves

end
