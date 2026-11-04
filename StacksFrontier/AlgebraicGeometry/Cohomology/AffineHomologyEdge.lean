module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.AlgebraicGeometry.AffineVanishingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine cohomology edge isomorphism, and conservativity of `RΓ` below a bound

Let `X` be a scheme over a commutative ring `A`. The unbounded right derived functor
`AlgebraicGeometry.derivedGlobalSectionsOver f` of `A`-linear global sections carries a canonical
*edge morphism*
$$ H^q(R\Gamma(X, E)) \longrightarrow \Gamma(X, H^q(E)) . $$
For `X` affine and `E` cohomologically bounded below with quasi-coherent cohomology, the edge
morphism is invertible; this is the bounded below case of [Stacks, Tag 08D4] over an affine base.
Consequently `RΓ(X, -)` is conservative on the bounded below complexes with quasi-coherent
cohomology: if `RΓ(X, E) = 0` then `E = 0`.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsHomologyComparison`: the edge morphism
  `H^q(RΓ(X, -)) ⟶ Γ(X, H^q(-))`.

## Main results

* `AlgebraicGeometry.isIso_derivedGlobalSectionsHomologyComparison_app_of_isGE`: over an affine
  base the edge morphism is invertible at a cohomologically bounded below object with
  quasi-coherent cohomology.
* `AlgebraicGeometry.isZero_of_isZero_globalSectionsOver_of_isQuasicoherent`: a quasi-coherent
  module on an affine scheme with vanishing `A`-linear global sections is zero.
* `AlgebraicGeometry.isZero_of_isZero_derivedGlobalSectionsOver_of_isGE`: over an affine base,
  `RΓ(X, -)` is conservative on the bounded below complexes with quasi-coherent cohomology.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### An object of a derived category with vanishing cohomology is zero -/

/-- An object of `D(𝒜)` all of whose cohomology objects vanish is zero. -/
private theorem isZero_of_forall_isZero_homologyFunctor_obj {𝒜 : Type*} [Category* 𝒜]
    [Abelian 𝒜] [HasDerivedCategory 𝒜] (Y : DerivedCategory 𝒜)
    (hz : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor 𝒜 n).obj Y)) : IsZero Y := by
  have hiso : IsIso (0 : Y ⟶ Y) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [(hz n).eq_of_src ((DerivedCategory.homologyFunctor 𝒜 n).map (0 : Y ⟶ Y)) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  calc (𝟙 Y) = CategoryTheory.inv (0 : Y ⟶ Y) ≫ (0 : Y ⟶ Y) := (IsIso.inv_hom_id _).symm
    _ = 0 := Limits.comp_zero

/-! ### The edge morphism of unbounded derived global sections -/

/-- The cohomology edge morphism `H^q(RΓ(X, E)) ⟶ Γ(X, H^q(E))` of `A`-linear derived global
sections: the unique natural transformation out of `RΓ(X, -) ⋙ H^q`, as a right derived functor of
`K ↦ H^q(Γ(X, K))`, extending the cohomology comparison on the homotopy category. -/
def derivedGlobalSectionsHomologyComparison (q : ℤ) :
    derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) q ⟶
      DerivedCategory.homologyFunctor X.Modules q ⋙ globalSectionsOver f :=
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
    (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) q

/-- Let `X` be an affine scheme over `A` and let `E` be an object of `D(𝒪_X)` which is
cohomologically bounded below and all of whose cohomology sheaves are quasi-coherent. Then the edge
morphism `H^q(RΓ(X, E)) ⟶ Γ(X, H^q(E))` is invertible for every `q`. -/
@[ega "III 1.3.1" "more general"]
theorem isIso_derivedGlobalSectionsHomologyComparison_app_of_isGE [IsAffine X] (q : ℤ)
    (E : DerivedCategory X.Modules) (n : ℤ) [E.IsGE n]
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) :
    IsIso ((derivedGlobalSectionsHomologyComparison f q).app E) :=
  Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) q E n
    fun j => have := hqc j
      rightAcyclic_globalSectionsOver_of_isQuasicoherent f
        ((DerivedCategory.homologyFunctor X.Modules j).obj E)

/-! ### Conservativity of global sections and of `RΓ` below a bound -/

/-- A quasi-coherent module on an affine scheme with vanishing `A`-linear global sections is
zero. -/
theorem isZero_of_isZero_globalSectionsOver_of_isQuasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (h : IsZero ((globalSectionsOver f).obj M)) : IsZero M := by
  have hs : Subsingleton ((globalSectionsOver f).obj M) := ModuleCat.isZero_iff_subsingleton.mp h
  exact _root_.Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine
    M (ModuleCat.isZero_iff_subsingleton.mpr hs)

/-- Over an affine base, an object of `D(𝒪_X)` which is cohomologically bounded below, has
quasi-coherent cohomology, and has vanishing unbounded derived global sections, is zero. -/
theorem isZero_of_isZero_derivedGlobalSectionsOver_of_isGE [IsAffine X]
    (E : DerivedCategory X.Modules) (n : ℤ) [E.IsGE n]
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (h : IsZero ((derivedGlobalSectionsOver f).obj E)) : IsZero E := by
  refine isZero_of_forall_isZero_homologyFunctor_obj E fun q => ?_
  have hq : IsIso ((derivedGlobalSectionsHomologyComparison f q).app E) :=
    isIso_derivedGlobalSectionsHomologyComparison_app_of_isGE f q E n hqc
  have h0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
      ((derivedGlobalSectionsOver f).obj E)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map_isZero h
  have := hqc q
  exact isZero_of_isZero_globalSectionsOver_of_isQuasicoherent f _
    (h0.of_iso (asIso ((derivedGlobalSectionsHomologyComparison f q).app E)).symm)

end AlgebraicGeometry

end
