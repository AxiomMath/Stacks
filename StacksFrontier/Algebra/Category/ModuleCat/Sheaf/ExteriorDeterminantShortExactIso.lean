module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a short exact sequence, in determinant form

Let `(X, O_X)` be a ringed space and let `0 → E' → E → E'' → 0` be a short exact sequence of
sheaves of `O_X`-modules which are finite locally free of constant ranks `r'`, `r' + k + 1` and
`k + 1`. [Stacks, Tag 0B38] asserts a canonical isomorphism

`det(E') ⊗_{O_X} det(E'') ⟶ det(E)`,

with `det` the determinant of [Stacks, Tag 0FJN] — the annihilator of the degree-one part of
the exterior algebra. This file assembles that isomorphism out of two things already proved:
the identification `⋀ʳ F ≅ det(F)` at constant rank `r` of [Stacks, Tag 0B37]
(`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`), and the
isomorphy of the top-exterior-power comparison
(`Stacks.SheafOfModules.TopWedge.isIso_detComparison`).

## Main definitions

* `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIso`: **the canonical isomorphism
  `det(E') ⊗ det(E'') ≅ det(E)`** at constant ranks.

## Main results

* `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIso_hom`: the equation pinning it
  down — it is the comparison of top exterior powers, read through the three identifications of
  Tag 0B37. Since that comparison is characterised by the wedge-and-lift formula
  `Stacks.SheafOfModules.TopWedge.detComparison_wedge`, so is this isomorphism.

## Implementation notes

**What is still not covered.** The three ranks are assumed constant. For a short exact sequence
of finite locally free sheaves the ranks are only locally constant, and that case is what remains
of Tag 0B38. It does not require the clopen rank decomposition of [Stacks, Tag 0B37]:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact` builds the
comparison out of a determinant summand `det(E')ₙ` with no rank hypothesis at all, and its
implementation notes list what the general case still needs. The constant-rank hypothesis on `E`
is genuinely used here, although `isIso_detComparison` does not need it: it is what
`determinantIsoExteriorPower` needs in order to identify `det(E)` with `⋀^{r'+k+1} E`.

**Why the ranks have to match.** The hypotheses force `rank E = rank E' + rank E''`, which is
automatic for a short exact sequence of finite locally free sheaves; nothing is assumed beyond
the Stacks hypotheses, and the degree of the middle exterior power is written `r' + (k + 1)`
rather than as a separate variable for exactly that reason.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf

universe u

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **Stacks 0B38 in determinant form, at constant rank.** For a short exact sequence
`0 → E' → E → E'' → 0` of sheaves of modules on a ringed space, with `E'`, `E''` and `E` finite
locally free of constant ranks `r'`, `k + 1` and `r' + k + 1`, there is a canonical isomorphism
`det(E') ⊗ det(E'') ≅ det(E)` of the determinants of [Stacks, Tag 0FJN] — the annihilator of the
degree-one part of the exterior algebra.

It is the comparison of top exterior powers of
`Stacks.SheafOfModules.TopWedge.detComparison`, which
`Stacks.SheafOfModules.TopWedge.isIso_detComparison` shows is an isomorphism, conjugated by the
identifications `⋀ʳ F ≅ det(F)` of [Stacks, Tag 0B37]. The map is pinned by
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIso_hom` to that top-exterior-power
comparison, which `Stacks.SheafOfModules.TopWedge.detComparison_wedge` in turn pins to the
wedge-and-lift formula of the source.

This is the CONSTANT-RANK form of the tag. The general case, where the ranks are only locally
constant, is carried by
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`. -/
@[stacks 0B38 "the canonical isomorphism det(E')⊗det(E'')≅det(E) in DETERMINANT form, for a \
short exact sequence of finite locally free sheaves of CONSTANT rank",
  sga "6 X 5.1" "special case",
  sga "6 X 6.2.7" "special case"]
noncomputable def determinantTensorDeterminantIso
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r' + (k + 1))] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj A''.determinant ≅
        A.determinant :=
  have := isIso_detComparison A' A A'' f g hfg hS r' k
  (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso ((A'.determinantIsoExteriorPower
      r').symm)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso
          ((A''.determinantIsoExteriorPower (k + 1)).symm)) ≪≫
    asIso (detComparison A' A A'' f g hfg hS r' k) ≪≫
      A.determinantIsoExteriorPower (r' + (k + 1))

/-- **The equation pinning the determinant isomorphism down.** It is the comparison of top
exterior powers, precomposed with the inverses of the identifications `⋀ʳ F ≅ det(F)` on the two
factors and postcomposed with that identification on the target. -/
theorem determinantTensorDeterminantIso_hom
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r' + (k + 1))] :
    (determinantTensorDeterminantIso A' A A'' f g hfg hS r' k).hom =
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map ((A'.determinantIsoExteriorPower
          r').inv)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).map
          ((A''.determinantIsoExteriorPower (k + 1)).inv)) ≫
        detComparison A' A A'' f g hfg hS r' k ≫
          (A.determinantIsoExteriorPower (r' + (k + 1))).hom :=
  rfl

end Stacks.SheafOfModules.TopWedge

end
