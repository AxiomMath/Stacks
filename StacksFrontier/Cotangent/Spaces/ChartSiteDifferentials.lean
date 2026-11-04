module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceLiftedRingedTopoi

/-!
# Differentials on the site of polynomial charts of an algebraic space, and their inverse image

Let `Λ` be a ring and let `X` be an algebraic space over `Λ`. On the site `C_{X/Λ}` of
polynomial charts of Tag 08VK the affine-functions sheaf `𝒪` is an algebra over the constant
sheaf `Λ̲` through the structure map `Λ̲ ⟶ 𝒪`, so it has a sheaf of relative differentials
`Ω_{𝒪/Λ̲}`, the sheaf of `𝒪`-modules corepresenting `Λ̲`-derivations of `𝒪` (Tag 04BL). The
horizontal arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of the diagram of Tag 08VK is the
identity on underlying topoi, and its module pullback `i^*` of Tag 03D6 carries `Ω_{𝒪/Λ̲}` to the
sheaf of `π⁻¹𝒪_X`-modules `i^*Ω_{𝒪/Λ̲}`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.chartStructureSheaf`: `π⁻¹𝒪_X`, the inverse image
  along `π` of the structure sheaf of the small étale site of `X`.
* `AlgebraicGeometry.Space.PolynomialChart.chartDifferentials` is `Ω_{𝒪/Λ̲}`, the sheaf of
  relative differentials of the affine-functions sheaf over the constant sheaf `Λ̲`, and
  `AlgebraicGeometry.Space.PolynomialChart.universalChartDerivation` is its universal
  derivation.
* `AlgebraicGeometry.Space.PolynomialChart.horizontalModuleInverseImage` is `i^*`, the pullback
  of sheaves of modules along the horizontal arrow of the diagram of Tag 08VK, and
  `AlgebraicGeometry.Space.PolynomialChart.pulledBackDifferentials` is `i^*Ω_{𝒪/Λ̲}`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.hasSheafify_addCommGrpCat_topology` and
  `AlgebraicGeometry.Space.PolynomialChart.wEqualsLocallyBijective_topology`: abelian presheaves
  on the chart site admit sheafification in the coefficient universe `u + 1`, and the maps
  sheafification inverts there are the locally bijective ones. These are what let sheaves of
  modules be pulled back along the arrows of the diagram.
* `AlgebraicGeometry.Space.PolynomialChart.existsUnique_desc_chartDerivation`: **Tag 04BL for
  the chart site.** Every `Λ̲`-derivation of `𝒪` with values in a sheaf of `𝒪`-modules factors
  through the universal derivation by a unique morphism of sheaves of modules.

## Implementation notes

The coefficient universe is `u + 1`: a polynomial chart carries a `Type u` set of variables and
an object of the small étale site of `X`, so `C_{X/Λ}` has objects in `Type (u + 1)` and
morphisms in `Type u`. Tag 04BL corepresents derivations in `SheafOfModules.{max u₁ v₁ w m}` for
a site with objects in `Type u₁`, morphisms in `Type v₁` and rings in `CommRingCat.{w}`, which
here is `u + 1` already at `m = u`.

Sheafification of abelian presheaves is not found by instance search at this universe: the site
is large, and what makes it available is that `C_{X/Λ}` is essentially small in `u + 1`, which
contains both its objects and its morphisms. The two statements above transport sheafification
from a small model and are seated as local instances.

`i^*` is `Stacks.Sheaves.RingedToposModules.pullbackModules` of the horizontal arrow, that is the
inverse image of Tag 03D2 followed by extension of scalars along `i♯`.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK), the diagram of ringed
  topoi of the polynomial charts of an algebraic space over a ring.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations by the sheaf of differentials.
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6), the pullback of
  sheaves of modules along a morphism of ringed topoi.
* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM), the lemma whose
  right-hand side is formed from `Ω_{𝒪/Λ̲}` and `i^*Ω_{𝒪/Λ̲}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-! ### Sheafification of abelian presheaves on the chart site -/

/-- Abelian presheaves on the chart site admit sheafification in the coefficient universe
`u + 1`: the site is essentially small there, since that universe contains both its objects and
its morphisms. -/
theorem hasSheafify_addCommGrpCat_topology :
    HasSheafify (topology Λ B hS X hX) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u + 1, u, u} (topology Λ B hS X hX)

/-- On the chart site, the maps that sheafification of abelian presheaves inverts in the
coefficient universe `u + 1` are the locally bijective ones. -/
theorem wEqualsLocallyBijective_topology :
    (topology Λ B hS X hX).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u + 1, u, u} (topology Λ B hS X hX)

/-! ### The differentials of the affine-functions sheaf -/

/-- `π⁻¹𝒪_X`: the inverse image along the projection `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)` of the
structure sheaf of the small étale site of `X`, the structure sheaf of the source of both arrows
of the diagram of Tag 08VK. -/
abbrev chartStructureSheaf : Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
    (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)

/-- `Ω_{𝒪/Λ̲}`: the sheaf of relative differentials of the affine-functions sheaf `𝒪` over the
constant sheaf `Λ̲` on the site of polynomial charts, taken along the structure map
`Λ̲ ⟶ 𝒪` of the diagram of Tag 08VK. -/
def chartDifferentials :
    _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := topology Λ B hS X hX)
        (liftedAffineSheaf Λ B hS X hX)) :=
  AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1, u + 1, u}
    (liftedConstantBaseSheaf Λ B hS X hX) (liftedAffineSheaf Λ B hS X hX)
      (liftedBaseSheafMap Λ B hS X hX)

/-- The universal `Λ̲`-derivation of `𝒪` with values in `Ω_{𝒪/Λ̲}`. -/
def universalChartDerivation :
    (chartDifferentials Λ B hS X hX).val.Derivation' (liftedBaseSheafMap Λ B hS X hX).hom :=
  AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1, u + 1, u}
    (liftedConstantBaseSheaf Λ B hS X hX) (liftedAffineSheaf Λ B hS X hX)
      (liftedBaseSheafMap Λ B hS X hX)

/-- **Tag 04BL for the site of polynomial charts of an algebraic space.** Every `Λ̲`-derivation
of `𝒪` with values in a sheaf of `𝒪`-modules factors through the universal derivation by a
unique morphism of sheaves of modules, so `Ω_{𝒪/Λ̲}` corepresents relative derivations on this
site. -/
theorem existsUnique_desc_chartDerivation
    (F : _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := topology Λ B hS X hX)
        (liftedAffineSheaf Λ B hS X hX)))
    (D : F.val.Derivation' (liftedBaseSheafMap Λ B hS X hX).hom) :
    ∃! f : chartDifferentials Λ B hS X hX ⟶ F,
      (universalChartDerivation Λ B hS X hX).postcomp f.val = D :=
  AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{u, u + 1, u + 1, u}
    (liftedConstantBaseSheaf Λ B hS X hX) (liftedAffineSheaf Λ B hS X hX)
      (liftedBaseSheafMap Λ B hS X hX) F D

/-! ### The inverse image along the horizontal arrow -/

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-- `i^*`, the pullback of sheaves of modules along the horizontal arrow
`i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of the diagram of Tag 08VK: the inverse image
of Tag 03D2 followed by extension of scalars along `i♯`. -/
def horizontalModuleInverseImage :
    _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := topology Λ B hS X hX)
          (liftedAffineSheaf Λ B hS X hX)) ⥤
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := topology Λ B hS X hX)
          (chartStructureSheaf Λ B hS X hX)) :=
  (liftedHorizontalHom Λ B hS X hX).toModulesHom.pullbackModules

/-- `i^*Ω_{𝒪/Λ̲}`, the sheaf of `π⁻¹𝒪_X`-modules obtained from the differentials of the
affine-functions sheaf by pullback along the horizontal arrow of the diagram of Tag 08VK. -/
abbrev pulledBackDifferentials :
    _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := topology Λ B hS X hX)
        (chartStructureSheaf Λ B hS X hX)) :=
  (horizontalModuleInverseImage Λ B hS X hX).obj (chartDifferentials Λ B hS X hX)

/-- `i^*` is additive, being a left adjoint of the direct image of sheaves of modules. -/
theorem horizontalModuleInverseImage_additive :
    (horizontalModuleInverseImage Λ B hS X hX).Additive :=
  AlgebraicGeometry.RingedToposHom.pullbackModules_additive (liftedHorizontalHom Λ B hS X hX)

end AlgebraicGeometry.Space.PolynomialChart

end
