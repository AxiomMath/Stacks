module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented

/-!
# The derived-fibre Euler characteristic of a derived pullback

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces and `K` an object of `D(𝒪_Y)` with
quasi-coherent cohomology, for instance a perfect object.  For a point `y'` of `Y'`, the derived
fibre of `Lg^*K` at `y'` is the derived fibre of `K` at `g(y')` read over the residue field of
`y'`: a field-valued point `p : Spec(k) ⟶ Y'` representing `y'` gives the field-valued point
`g ∘ p` of `Y` representing `g(y')`, and `Lp^* Lg^* K ≅ L(g ∘ p)^* K`.  Hence the derived-fibre
Betti numbers, and the derived-fibre Euler characteristic, of `Lg^*K` are those of `K` pulled back
along `|g| : |Y'| → |Y|`:

`χ(Lg^*K ⊗^𝐋 κ(y')) = χ(K ⊗^𝐋 κ(g(y')))`.

The functions are evaluated at chosen representatives of the points, and the representative
`g ∘ p` need not be the chosen one for `g(y')`; the two give the same values because `K` has
quasi-coherent cohomology (Stacks 03BU for derived fibres,
`AlgebraicGeometry.Space.derivedFibreBettiAt_eq_of_class_eq`).

## Main results

* `AlgebraicGeometry.Space.derivedFibreBetti_derivedPullback`: the derived-fibre Betti numbers of
  `Lg^*K` are those of `K` composed with `|g|`.
* `AlgebraicGeometry.Space.derivedFibreEuler_derivedPullback`: the same for the Euler
  characteristic, and `AlgebraicGeometry.Space.derivedFibreEuler_derivedPullback_of_isPerfect` for
  a perfect `K`.

## References

* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/- The standard model of the derived category is forced by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' Y : AlgebraicSpaces B S hS}

/-- **The derived-fibre Betti numbers of a derived pullback.**  For `g : Y' ⟶ Y` and an object `K`
of `D(𝒪_Y)` with quasi-coherent cohomology, the `n`-th derived-fibre Betti number of `Lg^*K` at a
point `y'` of `Y'` is that of `K` at `g(y')`. -/
theorem derivedFibreBetti_derivedPullback (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (n : ℤ) (x : points B S hS Y'.1) :
    derivedFibreBetti Y' ((smallEtaleDerivedModulePullback B S hS g).obj K) n x =
      derivedFibreBetti Y K n (pointsMap B S hS Y'.1 g.hom x) := by
  rw [derivedFibreBetti_apply, derivedFibreBetti_apply, derivedFibreBettiAt_derivedPullback]
  refine derivedFibreBettiAt_eq_of_class_eq B S hS Y K hK n ?_
  change Quot.mk _ _ = Quot.mk _ (Quot.out (pointsMap B S hS Y'.1 g.hom x))
  rw [Quot.out_eq]
  conv_rhs => rw [← Quot.out_eq x]
  rfl

/-- **The derived-fibre Euler characteristic of a derived pullback.**  For `g : Y' ⟶ Y` and an
object `K` of `D(𝒪_Y)` with quasi-coherent cohomology, `χ(Lg^*K ⊗^𝐋 κ(y')) = χ(K ⊗^𝐋 κ(g(y')))`
for every point `y'` of `Y'`. -/
theorem derivedFibreEuler_derivedPullback (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (x : points B S hS Y'.1) :
    derivedFibreEuler Y' ((smallEtaleDerivedModulePullback B S hS g).obj K) x =
      derivedFibreEuler Y K (pointsMap B S hS Y'.1 g.hom x) := by
  simp only [derivedFibreEuler_apply, derivedFibreBetti_derivedPullback g K hK]

/-- **The derived-fibre Euler characteristic of the derived pullback of a perfect object** is the
derived-fibre Euler characteristic of the object composed with the map on points. -/
theorem derivedFibreEuler_derivedPullback_of_isPerfect (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) (x : points B S hS Y'.1) :
    derivedFibreEuler Y' ((smallEtaleDerivedModulePullback B S hS g).obj K) x =
      derivedFibreEuler Y K (pointsMap B S hS Y'.1 g.hom x) :=
  derivedFibreEuler_derivedPullback g K (derivedCategoryB_of_isPerfect B S hS Y K hK) x

end AlgebraicGeometry.Space

end
