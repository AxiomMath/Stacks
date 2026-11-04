module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealEtaleFittingDescent

/-!
# Stacks 087B, with no hypothesis beyond the source's

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let
`φ : W ⟶ X` be a quasi-compact separated étale morphism, let `U ⊆ X` be a quasi-compact open
subspace and let `𝓘 ⊆ 𝒪_W` be a finite type quasi-coherent sheaf of ideals with
`V(𝓘) ∩ φ⁻¹(U) = ∅`.  Then there is a finite type quasi-coherent sheaf of ideals `𝓙 ⊆ 𝒪_X`
with `V(𝓙) ∩ U = ∅` and `φ⁻¹(𝓙) 𝒪_W = 𝓘 𝓘'` for some finite type quasi-coherent sheaf of
ideals `𝓘' ⊆ 𝒪_W`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `exists_isFiniteTypeQuasicoherentIdeal_disjoint_pullbackIdealSubsheaf_eq_idealSmul`
  is **Stacks 087B**.

## Implementation notes

The construction is
`AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul`,
which proves the same conclusion under the same hypotheses together with the statement of
Stacks 07VR, the input through which Stacks 0874 factors `φ`.  That input is
`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite`, so nothing is left over.

## References

* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 087B.**  Let `X` be a quasi-compact and quasi-separated algebraic space over `S`,
let `φ : W ⟶ X` be a quasi-compact separated étale morphism, let `U ⊆ X` be a quasi-compact
open subspace and let `𝓘 ⊆ 𝒪_W` be a finite type quasi-coherent sheaf of ideals with
`V(𝓘) ∩ φ⁻¹(U) = ∅`.  Then there is a finite type quasi-coherent sheaf of ideals `𝓙 ⊆ 𝒪_X`
such that

1. `V(𝓙) ∩ U = ∅`, and
2. `φ⁻¹(𝓙) 𝒪_W = 𝓘 𝓘'` for some finite type quasi-coherent sheaf of ideals `𝓘' ⊆ 𝒪_W`.

The inverse-image ideal `φ⁻¹(𝓙) 𝒪_W` is `AlgebraicGeometry.Space.pullbackIdealSubsheaf`, which
is defined for representable morphisms; a separated étale morphism is representable by
Stacks 0418, and the statement names that proof. -/
@[stacks 087B]
theorem exists_isFiniteTypeQuasicoherentIdeal_disjoint_pullbackIdealSubsheaf_eq_idealSmul
    {X W : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (φ : W ⟶ X) (hφqc : IsQuasiCompact B S hS φ.hom) (hφsep : IsSeparated B S hS φ.hom)
    (hφet : IsEtale B S hS φ.hom)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS W I)
    (hIU : Disjoint (idealZeroLocus B S hS W I)
      (subspacePointSet B S hS W.1 (U.preimage φ.hom))) :
    ∃ J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      IsFiniteTypeQuasicoherentIdeal B S hS X J ∧
        Disjoint (idealZeroLocus B S hS X J) (subspacePointSet B S hS X.1 U) ∧
        ∃ I' : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule,
          IsFiniteTypeQuasicoherentIdeal B S hS W I' ∧
            pullbackIdealSubsheaf B S hS φ
                (relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS φ.hom W.2 X.2
                  (isLocallyQuasiFinite_of_isEtale' B S hS hφet) hφsep) J =
              Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) I I' :=
  exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul
    (fun g hX hY hg hYqc hYqs =>
      exists_integralFiniteSystem_of_isFinite B S hS g hX hY hg hYqc hYqs)
    hXqc hXqs φ hφqc hφsep hφet U hU hUqc I hI hIU

end AlgebraicGeometry.Space
