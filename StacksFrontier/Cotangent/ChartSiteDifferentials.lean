module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartRingedTopoi

/-!
# Differentials on the site of polynomial charts, and their inverse image

Let `Λ` be a ring and let `X` be a scheme over `Λ`. On the site `C_{X/Λ}` of polynomial charts
of Tag 08VA the affine-functions sheaf `𝒪` is an algebra over the constant sheaf `Λ̲` through
the structure map of that diagram, so it has a sheaf of relative differentials `Ω_{𝒪/Λ̲}`, the
sheaf of `𝒪`-modules corepresenting `Λ̲`-derivations of `𝒪` (Tag 04BL). The horizontal arrow
`i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of the same diagram is the identity on
underlying topoi, and its module pullback `i^*` of Tag 03D6 carries `Ω_{𝒪/Λ̲}` to the sheaf of
`π⁻¹𝒪_X`-modules `i^*Ω_{𝒪/Λ̲}`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.chartDifferentials` is `Ω_{𝒪/Λ̲}`, the sheaf of relative
  differentials of the affine-functions sheaf over the constant sheaf `Λ̲`, formed in the
  coefficient universe of the chart topos, and
  `AlgebraicGeometry.PolynomialChart.universalChartDerivation` is its universal derivation.
* `AlgebraicGeometry.PolynomialChart.horizontalModuleInverseImage` is `i^*`, the pullback of
  sheaves of modules along the horizontal arrow of the diagram of Tag 08VA, and
  `AlgebraicGeometry.PolynomialChart.pulledBackDifferentials` is `i^*Ω_{𝒪/Λ̲}`.

## Main results

* `AlgebraicGeometry.PolynomialChart.hasSheafify_addCommGrpCat_topology` and
  `AlgebraicGeometry.PolynomialChart.wEqualsLocallyBijective_topology`: abelian presheaves on
  the chart site admit sheafification in the coefficient universe, and the maps sheafification
  inverts there are the locally bijective ones. These are what let sheaves of modules be
  pulled back along the arrows of the diagram.
* `AlgebraicGeometry.PolynomialChart.existsUnique_desc_chartDerivation`: **Tag 04BL for the
  chart site.** Every `Λ̲`-derivation of `𝒪` with values in a sheaf of `𝒪`-modules factors
  through the universal derivation by a unique morphism of sheaves of modules.

## Implementation notes

The coefficient universe is the `max w (u + 1)` of Tag 08VA: a polynomial chart carries a
`Type u` set of variables, so `C_{X/Λ}` has objects in `Type (u + 1)` and morphisms in
`Type u`. Tag 04BL corepresents derivations in `SheafOfModules.{max u₁ v₁ w m}` for a site with
objects in `Type u₁` and morphisms in `Type v₁` and rings in `CommRingCat.{w}`, which here is
`max w (u + 1)` already at `m = u`, so `Ω_{𝒪/Λ̲}` needs no specialization of universes.

Sheafification of abelian presheaves is not found by instance search at these universes: the
site is large, and what makes it available is that `C_{X/Λ}` is essentially small in the
coefficient universe, which contains both its objects and its morphisms. The two statements
above transport sheafification from a small model and are seated as local instances, as the
lower-shriek development does for the projection of a fibred category.

`i^*` is `Stacks.Sheaves.RingedToposModules.pullbackModules` of the horizontal arrow, that is
the inverse image of Tag 03D2 followed by extension of scalars along `i♯`. Since `i` is the
identity on underlying topoi, the inverse-image factor changes no sections; the scalars it
leaves the modules over are those of the inverse image of the ring sheaf along the identity,
which is a sheaf isomorphic to `𝒪` rather than `𝒪` itself.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA), the diagram of ringed
  topoi of the polynomial charts of a scheme over a ring.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations by the sheaf of differentials.
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6), the pullback of
  sheaves of modules along a morphism of ringed topoi.
* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9), the lemma whose
  right-hand side is formed from `Ω_{𝒪/Λ̲}` and `i^*Ω_{𝒪/Λ̲}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-! ### Sheafification of abelian presheaves on the chart site -/

/-- Abelian presheaves on the chart site admit sheafification in the coefficient universe: the
site is essentially small there, since that universe contains both its objects and its
morphisms. -/
theorem hasSheafify_addCommGrpCat_topology :
    HasSheafify (topology Λ X structureMap) AddCommGrpCat.{max w (u + 1)} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w (u + 1), u, u + 1}
    (topology Λ X structureMap)

/-- On the chart site, the maps that sheafification of abelian presheaves inverts in the
coefficient universe are the locally bijective ones. -/
theorem wEqualsLocallyBijective_topology :
    (topology Λ X structureMap).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, max w (u + 1),
    u + 1, max w (u + 1) + 1, max w (u + 1)} (topology Λ X structureMap)

/-! ### The differentials of the affine-functions sheaf -/

/-- `Ω_{𝒪/Λ̲}`: the sheaf of relative differentials of the affine-functions sheaf `𝒪` over the
constant sheaf `Λ̲` on the site of polynomial charts, taken along the structure map of the
diagram of Tag 08VA. -/
def chartDifferentials :
    _root_.SheafOfModules.{max w (u + 1)}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (topology Λ X structureMap)))
        (affineSheaf.{u, w} Λ X structureMap)) :=
  AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1,
    max w (u + 1), u} (constantBaseSheaf.{u, w} Λ X structureMap)
    (affineSheaf.{u, w} Λ X structureMap)
    (piSchemesDiagram.{u, w} Λ X structureMap).baseStructureMap

/-- The universal `Λ̲`-derivation of `𝒪` with values in `Ω_{𝒪/Λ̲}`. -/
def universalChartDerivation :
    (chartDifferentials.{u, w} Λ X structureMap).val.Derivation'
      (piSchemesDiagram.{u, w} Λ X structureMap).baseStructureMap.hom :=
  AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1,
    max w (u + 1), u} (constantBaseSheaf.{u, w} Λ X structureMap)
    (affineSheaf.{u, w} Λ X structureMap)
    (piSchemesDiagram.{u, w} Λ X structureMap).baseStructureMap

/-- **Tag 04BL for the site of polynomial charts.** Every `Λ̲`-derivation of `𝒪` with values in
a sheaf of `𝒪`-modules factors through the universal derivation by a unique morphism of sheaves
of modules, so `Ω_{𝒪/Λ̲}` corepresents relative derivations on this site. -/
theorem existsUnique_desc_chartDerivation
    (F : _root_.SheafOfModules.{max w (u + 1)}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (topology Λ X structureMap)))
        (affineSheaf.{u, w} Λ X structureMap)))
    (D : F.val.Derivation'
      (piSchemesDiagram.{u, w} Λ X structureMap).baseStructureMap.hom) :
    ∃! f : chartDifferentials.{u, w} Λ X structureMap ⟶ F,
      (universalChartDerivation.{u, w} Λ X structureMap).postcomp f.val = D :=
  AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{u, u + 1,
    max w (u + 1), u} (constantBaseSheaf.{u, w} Λ X structureMap)
    (affineSheaf.{u, w} Λ X structureMap)
    (piSchemesDiagram.{u, w} Λ X structureMap).baseStructureMap F D

/-! ### The inverse image along the horizontal arrow -/

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-- `i^*`, the pullback of sheaves of modules along the horizontal arrow
`i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of the diagram of Tag 08VA: the inverse image
of Tag 03D2 followed by extension of scalars along `i♯`. -/
def horizontalModuleInverseImage :
    _root_.SheafOfModules.{max w (u + 1)}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (topology Λ X structureMap)))
          (affineSheaf.{u, w} Λ X structureMap)) ⥤
      _root_.SheafOfModules.{max w (u + 1)}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (topology Λ X structureMap)))
          (chartStructureSheaf.{u, w} Λ X structureMap)) :=
  ((piSchemesDiagram.{u, w} Λ X structureMap).horizontal).toModulesHom.pullbackModules

/-- `i^*Ω_{𝒪/Λ̲}`, the sheaf of `π⁻¹𝒪_X`-modules obtained from the differentials of the
affine-functions sheaf by pullback along the horizontal arrow of the diagram of Tag 08VA. -/
abbrev pulledBackDifferentials :
    _root_.SheafOfModules.{max w (u + 1)}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (topology Λ X structureMap)))
        (chartStructureSheaf.{u, w} Λ X structureMap)) :=
  (horizontalModuleInverseImage.{u, w} Λ X structureMap).obj
    (chartDifferentials.{u, w} Λ X structureMap)

/-- `i^*` is additive, being a left adjoint of the direct image of sheaves of modules. -/
theorem horizontalModuleInverseImage_additive :
    (horizontalModuleInverseImage.{u, w} Λ X structureMap).Additive :=
  AlgebraicGeometry.RingedToposHom.pullbackModules_additive
    ((piSchemesDiagram.{u, w} Λ X structureMap).horizontal)

end AlgebraicGeometry.PolynomialChart

end
