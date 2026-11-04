module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartQuasicoherentDerived

/-!
# `QC((Aff/S), O)` is `D_QCoh(O_S)` (Stacks 0H00)

Let `S` be a scheme. **Stacks 0H00** (a remark of Derived Categories of Schemes, Section 0GZY,
whose proof is Sheaves on Stacks, Proposition 0H0K) says that the triangulated category
`QC((Aff/S), O)` of Cohomology on Sites, Definition 0GYV — for the category `(Aff/S)` of affine
schemes over `S` with the chaotic topology and its sheaf of rings `O` of global functions — is
canonically equivalent to `D_QCoh(O_S)`.

Here `(Aff/S)` is the affine subcategory `(Sch/S)_{affine}` of the big fppf category of `S`
(Stacks 0H0A for the identity of `(Sch/S)_{fppf}`), so `QC((Aff/S), O)` is
`AlgebraicGeometry.Stack.quasiCoherentDerived` of Stacks 0H0H for the identity of `(Sch/S)_{fppf}`:
the full subcategory of `D((Aff/S), O)` of the objects `K` with
`RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` invertible for every morphism `U ⟶ V` of `(Aff/S)`.
`D_QCoh(O_S)` is the full subcategory of the derived category of `O_S`-modules, on the ringed
space `S`, of the objects with quasi-coherent cohomology sheaves, in any model of that derived
category.

## The proof

It is the proof of Stacks 0H0K, run with the Zariski topology and the affine opens of `S` in place
of the étale topology and the affine étale charts of an algebraic space:

1. `QC((Aff/S), O)` is the subcategory of Stacks 0GZS of the lift `X↑` of `(Aff/S)_{Zar}`: the
   objects `K` of `D(X↑)` with `Rε_*K` cartesian (Stacks 0H0J for the Zariski topology,
   `AlgebraicGeometry.Stack.quasiCoherentDerivedZariskiLiftedCartesianEquivalence`).
2. The affine opens of `S` form a full, cocontinuous subsite of `(Aff/S)_{Zar}` with the same
   structure sheaf; the direct image and the derived pullback along the resulting morphism of
   ringed sites `X↑ ⟶ Y↑` to the lift `Y↑` of the small affine Zariski site of `S` restrict to
   mutually inverse equivalences of the 0GZS subcategories (the argument of Stacks 09J1,
   `AlgebraicGeometry.ZariskiCharts.liftedAffineOpensCartesianEquivalence`).
3. The 0GZS subcategory of `D(Y↑)` is `D_QCoh(O_S)`
   (`AlgebraicGeometry.ZariskiCharts.zariskiChartCartesianEquivalenceQuasicoherentDerived`):
   `O_S`-modules are sheaves of modules on the affine opens (Descent, Remark 03FG and the
   Comparison Lemma of Stacks 0F1B), and quasi-coherent ones are exactly the cartesian ones.

## Universes

The category `(Aff/S)` has its objects in `Type (u + 1)`, `S` being a scheme in `Type u`, so the
modules of `QC((Aff/S), O)` have their sections in `max (u + 1) t` for a free universe `t`, and
`D_QCoh(O_S)` is read at the same module universe. This cannot be lowered to `u`: the free
module on a set in `Type (u + 1)` lies in `QC((Aff/S), O)`.

## Main definitions

* `AlgebraicGeometry.Stack.affineBigSiteQuasiCoherentDerivedEquivalence`: **Stacks 0H00**, the
  equivalence `QC((Aff/S), O) ≌ D_QCoh(O_S)`.

## References

* [Stacks Project, Tag 0H00](https://stacks.math.columbia.edu/tag/0H00)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.ZariskiCharts

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0H00.** Let `S` be a scheme in a big fppf site `B`. Then `QC((Aff/S), O)` — the
triangulated category of quasi-coherent objects (Stacks 0GYV) of the derived category of
`O`-modules on the category `(Aff/S)` of affine schemes over `S` with the chaotic topology and
its sheaf of rings of global functions, that is `QC((Sch/S)_{fppf})` of Stacks 0H0H for the
identity of `(Sch/S)_{fppf}` — is canonically equivalent to `D_QCoh(O_S)`, the full subcategory
of the derived category of `O_S`-modules (in any model) of the objects with quasi-coherent
cohomology sheaves; the modules have their sections in `max (u + 1) t`.

The equivalence is the composite of the three equivalences of the proof of Stacks 0H0K, for the
Zariski topology: `ε^*` from `QC((Aff/S), O)` onto the objects `K` of `D((Aff/S)_{Zar}↑)` with
`Rε_*K` cartesian (Stacks 0H0J, 0GZS); the direct image along the morphism of ringed sites given
by the affine opens of `S`, inverse to the derived pullback on the 0GZS subcategories (the
argument of Stacks 09J1); and the identification of the 0GZS subcategory of the lifted small
affine Zariski site of `S` with `D_QCoh(O_S)` (Descent 03FG, Stacks 0F1B, 0H04). -/
@[stacks 0H00]
def affineBigSiteQuasiCoherentDerivedEquivalence
    [HasDerivedCategory (SheafOfModules.{max (u + 1) t} S.ringCatSheaf)] :
    quasiCoherentDerived.{u, u + 1, u, t} B S hS (𝟭 (BigFppfOver B S hS)) ≌
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite S.ringCatSheaf :
        ObjectProperty (SheafOfModules.{max (u + 1) t} S.ringCatSheaf))).FullSubcategory :=
  (quasiCoherentDerivedZariskiLiftedCartesianEquivalence.{u, u + 1, u, t} B S hS
      (𝟭 (BigFppfOver B S hS)) CategoryTheory.Functor.isFiberedInGroupoids_id).trans <|
    (liftedAffineOpensCartesianEquivalence.{u, t} B S hS (𝟭 (BigFppfOver B S hS))
      CategoryTheory.Functor.isFiberedInGroupoids_id rfl).symm.trans
    (zariskiChartCartesianEquivalenceQuasicoherentDerived.{u, t} B S hS)

/-- The functor of `AlgebraicGeometry.Stack.affineBigSiteQuasiCoherentDerivedEquivalence`: `ε^*`
to the lifted `(Aff/S)_{Zar}`, then the direct image along the affine opens of `S`, then the
identification with `D_QCoh(O_S)`. -/
theorem affineBigSiteQuasiCoherentDerivedEquivalence_functor
    [HasDerivedCategory (SheafOfModules.{max (u + 1) t} S.ringCatSheaf)] :
    (affineBigSiteQuasiCoherentDerivedEquivalence.{u, t} B S hS).functor =
      (quasiCoherentDerivedZariskiLiftedCartesianEquivalence.{u, u + 1, u, t} B S hS
          (𝟭 (BigFppfOver B S hS)) CategoryTheory.Functor.isFiberedInGroupoids_id).functor ⋙
        (liftedAffineOpensCartesianEquivalence.{u, t} B S hS (𝟭 (BigFppfOver B S hS))
          CategoryTheory.Functor.isFiberedInGroupoids_id rfl).inverse ⋙
        (zariskiChartCartesianEquivalenceQuasicoherentDerived.{u, t} B S hS).functor :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.affineBigSiteQuasiCoherentDerivedEquivalence`: the
identification of `D_QCoh(O_S)` with the 0GZS subcategory of the lifted small affine Zariski
site of `S`, then the derived pullback along the affine opens of `S`, then `Rε_*`. -/
theorem affineBigSiteQuasiCoherentDerivedEquivalence_inverse
    [HasDerivedCategory (SheafOfModules.{max (u + 1) t} S.ringCatSheaf)] :
    (affineBigSiteQuasiCoherentDerivedEquivalence.{u, t} B S hS).inverse =
      (zariskiChartCartesianEquivalenceQuasicoherentDerived.{u, t} B S hS).inverse ⋙
        (liftedAffineOpensCartesianEquivalence.{u, t} B S hS (𝟭 (BigFppfOver B S hS))
          CategoryTheory.Functor.isFiberedInGroupoids_id rfl).functor ⋙
        (quasiCoherentDerivedZariskiLiftedCartesianEquivalence.{u, u + 1, u, t} B S hS
          (𝟭 (BigFppfOver B S hS)) CategoryTheory.Functor.isFiberedInGroupoids_id).inverse :=
  rfl

end AlgebraicGeometry.Stack
