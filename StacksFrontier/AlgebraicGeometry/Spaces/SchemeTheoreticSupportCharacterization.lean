module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportEtaleChart
import StacksCore.Tactic.StacksAttribute

/-!
# The scheme-theoretic support of a finite type quasi-coherent module, in one statement

Let `X` be an algebraic space over a scheme `S` and let `F` be a finite type quasi-coherent
`𝒪_X`-module. Stacks 07U0 asserts that there is a smallest closed subspace `i : Z → X` for which
there is a quasi-coherent `𝒪_Z`-module `G` with `i_*G ≅ F`, and that moreover

1. for every scheme `U` with an étale morphism `φ : U → X`, the closed subscheme `Z ×_X U` is
   the scheme-theoretic support of `φ^*F`;
2. `G` is unique up to unique isomorphism;
3. `G` is of finite type;
4. the supports of `G` and of `F` are `|Z|`.

This file states the lemma as one assertion about the scheme-theoretic support
`AlgebraicGeometry.Space.schemeTheoreticSupport` of `F` and proves it.

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticSupport_isSmallest_and_properties`: **Stacks 07U0.**

## Implementation notes

The smallest closed subspace is `AlgebraicGeometry.Space.schemeTheoreticSupport`, the closed
subspace cut out by the annihilator ideal sheaf of `F`; the source instead descends the
scheme-theoretic supports of the restrictions of `F` to an étale presentation, and part (1) is
exactly the statement that the two constructions agree. Minimality is stated against every
closed subspace from which `F` is a direct image, without asking the module on it to be
quasi-coherent, which is the stronger form; the module on the support produced by existence is
quasi-coherent.

Part (1) is stated for an étale scheme chart `A` of `X`, an object of the small étale site: a
scheme `U` with an étale morphism to `X`. The restriction of `F` to `U` is
`AlgebraicGeometry.Space.chartRestrictionSheaf`, a quasi-coherent module of finite type on the
scheme `U`, and its scheme-theoretic support is that of Stacks 05JV; the closed subscheme
`Z ×_X U` is the ideal sheaf `AlgebraicGeometry.Space.idealSheafDataOfChart` that `Z` cuts out
on `U`.

## References

* [Stacks Project, Lemma 67.15.3 (Tag 07U0)](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 05JV](https://stacks.math.columbia.edu/tag/05JV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **Stacks 07U0.** Let `F` be a finite type quasi-coherent `𝒪_X`-module on an algebraic
space `X`. Its scheme-theoretic support `Z` is a closed subspace of `X` carrying a
quasi-coherent `𝒪_Z`-module `G` with `i_*G ≅ F`, and it is the smallest closed subspace from
which `F` is a direct image. Moreover:

1. on every étale scheme chart `U` of `X`, the scheme-theoretic support of the restriction of
   `F` to `U` is `Z ×_X U`;
2. a module `G` on `Z` with `i_*G ≅ F` is unique up to unique isomorphism;
3. such a `G` is of finite type;
4. the support of `F` is `|Z|`, and the support of such a `G` is all of `|Z|`. -/
@[stacks 07U0]
theorem schemeTheoreticSupport_isSmallest_and_properties (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F),
      -- existence of a quasi-coherent module on `Z` whose direct image is `F`
      (∃ G : Modules.{u, u} B S hS
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2,
        G.IsQuasicoherentOnSite ∧ Nonempty ((modulePushforward B S hS
          (closedSubspaceInclusion B S hS X
            ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F)) ∧
      -- minimality
      (∀ (Z' : ClosedSubspaces B S hS X.1)
        (G' : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z').1
          (closedSubspaceToSpace B S hS X Z').2),
        ((modulePushforward B S hS (closedSubspaceInclusion B S hS X Z')).obj G' ≅ F) →
          schemeTheoreticSupport B S hS X F ≤ Z'.1) ∧
      -- part (1)
      (∀ A : SmallEtale B S hS X.1,
        letI : (chartRestrictionSheaf B S hS X F A).IsQuasicoherent :=
          isQuasicoherent_chartRestrictionSheaf B S hS X F hF A
        letI : (chartRestrictionSheaf B S hS X F A).IsFiniteType :=
          Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections
            (chartRestrictionSheaf B S hS X F A)
            (moduleFinite_sections_chartRestrictionSheaf B S hS X F hF hFft A)
        Scheme.Modules.schemeTheoreticSupport (chartRestrictionSheaf B S hS X F A) =
          idealSheafDataOfChart B S hS X
            (definingIdealSheaf B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩)
            (definingIdealSheaf_isCartesianOnAffineCharts B S hS X
              ⟨schemeTheoreticSupport B S hS X F, hZ⟩) A) ∧
      -- part (2)
      (∀ (G H : Modules.{u, u} B S hS
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2)
        (eG : (modulePushforward B S hS (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F)
        (eH : (modulePushforward B S hS (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj H ≅ F),
        ∃! φ : G ≅ H, (modulePushforward B S hS (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).map φ.hom ≫ eH.hom = eG.hom) ∧
      -- part (3)
      (∀ (G : Modules.{u, u} B S hS
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2),
        ((modulePushforward B S hS (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F) →
          SheafOfModules.IsFiniteTypeOnSite G) ∧
      -- part (4)
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) =
          Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X F).toFunctor
            (schemeTheoreticSupport B S hS X F).ι) ∧
      (∀ (G : Modules.{u, u} B S hS
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
          (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2),
        ((modulePushforward B S hS (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F) →
          supportOfSheaf B S hS
            (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
            ((SheafOfModules.toSheaf _).obj G) = Set.univ) := by
  have hft := Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft
  obtain ⟨hZ, hG⟩ := exists_module_on_schemeTheoreticSupport B S hS X F hF hft
  refine ⟨hZ, hG, fun Z' G' e => schemeTheoreticSupport_le B S hS X F Z' G' e,
    fun A => schemeTheoreticSupport_chartRestrictionSheaf B S hS X F hF hFft _ rfl A,
    fun G H eG eH => module_on_closedSubspace_unique B S hS X F _ G H eG eH,
    fun G e => isFiniteTypeOnSite_module_on_closedSubspace B S hS X F hFft _ G e,
    supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft,
    fun G e => supportOfSheaf_module_on_schemeTheoreticSupport_eq_univ B S hS X F hF hFft _ rfl
      G e⟩

end AlgebraicGeometry.Space

end
