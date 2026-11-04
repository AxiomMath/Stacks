module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleNoetherianFibreCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality

/-!
# Critère de platitude par fibres over a locally Noetherian base, on genuine fibres

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` with `X`,
`Y`, `Z` locally Noetherian, let `F` be a coherent `𝒪_X`-module, let `x ∈ |X|` with images
`y ∈ |Y|` and `z ∈ |Z|`, and suppose `F_{x̄} ≠ 0` for a geometric point `x̄` over `x`.  Stacks
0APR says that the following are equivalent:

1. `F` is flat over `Z` at `x`, and the restriction of `F` to its fibre over `z` is flat at `x`
   over the fibre of `Y` over `z`;
2. `Y` is flat over `Z` at `y`, and `F` is flat over `Y` at `x`.

This file states and proves it with every notion read in the source's own terms.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_comp_and_isFlatOnFibreAtFieldValuedPoint_iff`:
  **Stacks 0APR.**

## Implementation notes

* Flatness of `F` over `Z` and over `Y` at `x` is `AlgebraicGeometry.Space.IsFlatOverAtPoint`,
  the definition of Stacks 05VV at a point of `|X|` (the chart condition (1) of Stacks 05VU),
  and flatness of `Y` over `Z` at `y` is `AlgebraicGeometry.Space.IsFlatAt` of Stacks 03ML.
* The fibre clause is `AlgebraicGeometry.Space.IsFlatOnFibreAtFieldValuedPoint`, condition (2) of
  Stacks 05WY: the pullback of `F` to the fibre product `X_z = Spec(K) ×_{z, Z} X` is flat, in the
  sense of Stacks 05VV, over `Y_z = Spec(K) ×_{z, Z} Y` at the `K`-rational point given by a
  field-valued point `Spec(K) ⟶ X` in the class of `x`.  The theorem holds for every such
  representative.
* `F` is coherent in the sense of Stacks 07UA (`AlgebraicGeometry.Space.IsCoherent`), which
  includes quasi-coherence; local Noetherianity of `X`, `Y`, `Z` is the étale-local scheme
  property of Stacks 03E6, which is how the source's hypothesis reads for algebraic spaces.

The proof is the reduction to the étale local rings.  Stacks 05WY (1) `⟺` (2),
`AlgebraicGeometry.Space.isFlatOnFibreAtFieldValuedPoint_iff_isFibreFlatOverAtGeometricPoint`,
turns the fibre clause into the geometric-stalk condition at `x̄`; Stacks 05VU turns the two
conditions of Stacks 05VV into flatness of `F_{x̄}` over the étale local rings; coherence gives
finiteness of `F_{x̄}` over `𝒪_{X, x̄}`; and the statement at the étale local rings is
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_and_isFlatOnFibre_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleNoetherianFibreCriterion.lean`, which is
Stacks 00MP and base change of flatness.

## References

* [Stacks Project, Tag 0APR](https://stacks.math.columbia.edu/tag/0APR)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 039B](https://stacks.math.columbia.edu/tag/039B)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0APR.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian
algebraic spaces over `S`, let `F` be a coherent `𝒪_X`-module and let `x ∈ |X|`, with image
`y ∈ |Y|`.  Suppose `F_{x̄} ≠ 0` for a geometric point `x̄` of `X` over `x`.  Then for every
field-valued point `Spec(K) ⟶ X` in the class of `x` the following are equivalent:

1. `F` is flat over `Z` at `x`, and the pullback of `F` to the fibre `X_z = Spec(K) ×_Z X` over
   the image `z` of the point is flat over `Y_z = Spec(K) ×_Z Y` at the `K`-rational point of
   `X_z`;
2. `Y` is flat over `Z` at `y`, and `F` is flat over `Y` at `x`.

Flatness at a point is the definition of Stacks 05VV for modules and of Stacks 03ML for
morphisms. -/
@[stacks 0APR "The full statement: flatness of F over Z and over Y at x is the definition of
  Stacks 05VV (IsFlatOverAtPoint), flatness of Y over Z at y is that of Stacks 03ML, and the
  fibre clause is flatness of the pullback of F to the fibre product Spec(K) x_Z X over
  Spec(K) x_Z Y at the K-point, for every field-valued representative of x (condition (2) of
  Stacks 05WY); F is coherent and X, Y, Z are locally Noetherian."]
theorem isFlatOverAtPoint_comp_and_isFlatOnFibreAtFieldValuedPoint_iff
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X.1) (xbar : GeometricPoint B S hS X.1) (hxbar : xbar.LiesOver x)
    (hne : Nontrivial (geometricModuleStalk B S hS X xbar F))
    (p : FieldValuedPoint B S hS X.1) (hp : p.class B S hS X.1 = x) :
    (IsFlatOverAtPoint B S hS X.2 (f ≫ g).hom F x ∧
        IsFlatOnFibreAtFieldValuedPoint B S hS f g p F) ↔
      (IsFlatAt B S hS g.hom (pointsMap B S hS X.1 f.hom x) ∧
        IsFlatOverAtPoint B S hS X.2 f.hom F x) := by
  subst hxbar
  have hfin : Module.Finite (etaleLocalRing B S hS X.1 xbar)
      (geometricModuleStalk B S hS X xbar F) :=
    module_finite_geometricModuleStalk B S hS X F inferInstance
      (Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType F inferInstance) xbar
  have hfibre : IsFlatOnFibreAtFieldValuedPoint B S hS f g p F ↔
      IsFlatOnFibreAtGeometricPoint B S hS f g F xbar :=
    (isFlatOnFibreAtFieldValuedPoint_iff_isFibreFlatOverAtGeometricPoint B S hS f g p F
      xbar.image xbar rfl hp).trans
      (Module.flat_quotient_smul_top_iff_flatQuotSMul _ _ _ (Ideal.map_map _ _).symm _).symm
  rw [hfibre]
  exact (and_congr (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar)
      Iff.rfl).trans ((isFlatOverAtGeometricPoint_and_isFlatOnFibre_iff B S hS f g F hX hY hZ
        xbar hfin hne).trans (and_congr Iff.rfl
          (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F xbar).symm))

end AlgebraicGeometry.Space

end
