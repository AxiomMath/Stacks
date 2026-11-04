module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionGeneratingLocus

/-!
# A section of an invertible module is a generator over its generating locus

Let `X` be an algebraic space over a scheme `S`, let `𝓜` be an invertible `𝒪_X`-module and let
`s` be a global section of `𝓜`, the map `φ_s : 𝒪_X ⟶ 𝓜`, `1 ↦ s`.  For an étale morphism
`g : Y ⟶ X` whose image lies in the generating locus of `s` — for instance the inclusion of the
generating subspace `U_s` — the pullback `g^* φ_s` is an isomorphism, so that
`g^* 𝓜 ≅ 𝒪_Y` through `s`; this is the identification `𝓛^{⊗ d}|_U ≅ 𝒪_U` in the proof of
Stacks 0D2W.

The pullback is a left adjoint, so it carries the cokernel of `φ_s` to the cokernel of
`g^* φ_s`; the support of the former pulls back to the support of the latter (Stacks 04KA for
étale `g`), which is empty because the image of `g` misses the support of the cokernel of `φ_s`.
So `g^* φ_s` is an epimorphism from `𝒪_Y` onto the invertible module `g^* 𝓜`, hence an
isomorphism by `AlgebraicGeometry.Space.isIso_of_epi_of_isInvertibleModule` (an epimorphism
between invertible modules is an isomorphism), the structure sheaf being invertible by
`AlgebraicGeometry.Space.isInvertibleModule_structureModule`.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullback_map_of_range_subset_sectionGeneratingLocus`: the
  pullback of `φ_s` along an étale morphism with image in the generating locus is invertible.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] smallEtaleModulesAbelian

/-- **A section of an invertible module generates its pullback to the generating locus.**  For an
étale morphism `g : Y ⟶ X` whose image lies in the generating locus of the global section `s` of
the invertible `𝒪_X`-module `𝓜`, the pullback along `g` of the map `𝒪_X ⟶ 𝓜`, `1 ↦ s`, is an
isomorphism. -/
theorem isIso_modulePullback_map_of_range_subset_sectionGeneratingLocus
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : IsInvertibleModule X M) (s : M.sections)
    (hrange : Set.range (pointsMap B S hS Y.1 g.hom) ⊆ sectionGeneratingLocus B S hS M s) :
    IsIso ((modulePullback B S hS g).map (M.unitHomEquiv.symm s)) := by
  set φ := M.unitHomEquiv.symm s with hφ
  have hadd : (modulePullback B S hS g).Additive :=
    (modulePullbackAdjunction B S hS g).left_adjoint_additive
  have hpres : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    (modulePullbackAdjunction B S hS g).leftAdjoint_preservesColimits
  have hcoker : IsZero ((modulePullback B S hS g).obj (cokernel φ)) := by
    refine (supportOfSheaf_eq_empty_iff_isZero.{u, u} B S hS Y
      ((modulePullback B S hS g).obj (cokernel φ))).1 ?_
    rw [supportOfSheaf_modulePullback_of_isEtale B S hS g hg]
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    exact hrange ⟨y, rfl⟩ hy
  have hepi : Epi ((modulePullback B S hS g).map φ) := by
    refine (Preadditive.epi_iff_isZero_cokernel _).2 ?_
    exact hcoker.of_iso (PreservesCokernel.iso (modulePullback B S hS g) φ).symm
  have hinv : IsInvertibleModule Y ((modulePullback B S hS g).obj M) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertible_modulePullback_obj B S hS g M
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hM))
  let e : structureSheafModule B S hS Y ≅
      (modulePullback B S hS g).obj (structureSheafModule B S hS X) :=
    Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (smallEtaleRingedToposModulesHom B S hS g)
  have : Epi (e.hom ≫ (modulePullback B S hS g).map φ) :=
    @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso e.hom) _ hepi
  have := isIso_of_epi_of_isInvertibleModule (isInvertibleModule_structureModule Y) hinv
    (e.hom ≫ (modulePullback B S hS g).map φ)
  exact (isIso_comp_left_iff e.hom _).1 this

end AlgebraicGeometry.Space

end
