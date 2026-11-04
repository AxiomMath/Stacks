module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic

/-!
# Extending a generic trace on differential forms to the reflexive hull

Let `f : Y ⟶ X` be a finite morphism of integral locally Noetherian schemes over a scheme `S`,
with `X` normal, and let `i ≥ 1`.  The direct image `f_*Ω^i_{Y/S}` is coherent, so a linear map
of generic stalks `(f_*Ω^i_{Y/S})_η ⟶ (Ω^i_{X/S})_η` that preserves the images of the stalks at
every point of codimension one extends in exactly one way to a map of `𝒪_X`-modules

`f_*Ω^i_{Y/S} ⟶ (Ω^i_{X/S})^∨∨`.

This is the extension step of a trace map in positive characteristic: the trace map of
[Stacks, Tag 0AX5] on the generic fibre is such a map of generic stalks, and the uniqueness of
the extension is what makes the resulting map on sheaves canonical.

## Main results

* `AlgebraicGeometry.existsUnique_lift_toReflexiveHull_relativeDifferentialForms`: a linear map
  of generic stalks satisfying the codimension-one condition extends uniquely to a map from
  `f_*Ω^i_{Y/S}` into the reflexive hull of `Ω^i_{X/S}`.
* `AlgebraicGeometry.genericFormsStalkEquiv`: the canonical identification of the generic
  stalk of `Ω^n_{X/S}` with `⋀ⁿ Ω_{K/Λ}`, for `K` the function field of `X` and `Λ` the local
  ring of `S` below the generic point.

## Implementation notes

`Ω^i_{X/S}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`, the `i`-th graded piece
of the exterior algebra of `Ω_{X/S}`; its coherence is
`AlgebraicGeometry.Scheme.Modules.isCoherent_exteriorPower` applied to a coherent `Ω_{X/S}` on a
locally Noetherian scheme, and it is assumed here as an instance so that the statement does not
presuppose which of the two is the primitive hypothesis.  Coherence of the direct image is
[Stacks, Tag 01Y6].

On `X` the identification of the generic stalk is constructed, not assumed: the stalk of an
exterior power is the exterior power of the stalk by `SheafOfModules.exteriorPowerStalkEquiv`,
and the stalk of `Ω_{X/S}` is `Ω[𝒪_{X,x}⁄𝒪_{S,q x}]` by
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`.  Composing them
forces the base ring `Λ` of the Kähler differentials to be the local ring of `S` below the
generic point of `X`, and the algebra structure on the function field to be the stalk map of
`q`, which is what the source means by `Ω_{X/S}` at the generic point.  The scalar ring has to
be re-ascribed to `X.functionField` once, because instance search matches at reducible
transparency and does not unfold the function field to a stalk of the structure sheaf.

The codimension-one condition is a hypothesis here: it is step 2 of the source's proof, where
the local ring of `Y` above a codimension-one point of `X` is shown to be a discrete valuation
ring of the form `A[x]/(xᵖ - a)`.  Stacks 0AX6 itself is
`AlgebraicGeometry.existsUnique_higherTraceExtension_relativeDifferentials`.

## References

* [Stacks Project, Tag 0AX5](https://stacks.math.columbia.edu/tag/0AX5)
* [Stacks Project, Tag 0AX6](https://stacks.math.columbia.edu/tag/0AX6)
* [Stacks Project, Tag 0AY7](https://stacks.math.columbia.edu/tag/0AY7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.RelativeDifferentialStalkMap
open scoped KaehlerDifferential

universe u

namespace AlgebraicGeometry

/-- A linear map from the generic stalk of `f_*Ω^{t+1}_{Y/S}` to the generic stalk of
`Ω^{t+1}_{X/S}` which, at every point of codimension one, carries the image of the source stalk
into the image of the target stalk extends to a map of `𝒪_X`-modules
`f_*Ω^{t+1}_{Y/S} ⟶ (Ω^{t+1}_{X/S})^∨∨` in exactly one way.  Existence is the criterion of
[Stacks, Tag 0AY7]; uniqueness holds because the reflexive hull is torsion free. -/
theorem existsUnique_lift_toReflexiveHull_relativeDifferentialForms {S X Y : Scheme.{u}}
    (p : X ⟶ S) (f : Y ⟶ X) (t : ℕ)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X] [IsFinite f]
    [(Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)).IsCoherent]
    [(Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ)).IsCoherent]
    (T : (((Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ))).presheaf.stalk
            (genericPoint X)) →ₗ[X.functionField]
        ((Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)).presheaf.stalk
          (genericPoint X)))
    (hT : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
      Set.MapsTo T
        (Set.range (((Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p)
            ((t + 1 : ℕ) : ℤ))).presheaf.stalkSpecializes h))
        (Set.range ((Scheme.Hom.relativeDifferentialForms p
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes h))) :
    ∃! Tr : (Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ)) ⟶
        reflexiveHull (Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)),
      ∀ m, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) Tr)) m =
        ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X)
            (toReflexiveHull (Scheme.Hom.relativeDifferentialForms p
              ((t + 1 : ℕ) : ℤ))).1)) (T m) :=
  existsUnique_lift_toReflexiveHull_of_codimension_one X _ _ T hT

/-- Transport an exterior power along a linear equivalence of the underlying modules. -/
noncomputable def extCongr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (e : M ≃ₗ[R] N) :
    (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

/-- **The stalk of `Ω^n_{X/S}` at a point `x` is `⋀ⁿ Ω[𝒪_{X,x}⁄𝒪_{S,q x}]`**: the stalk of an
exterior power is the exterior power of the stalk, and the stalk of `Ω_{X/S}` is the module of
Kähler differentials of the stalk map of `q`. -/
noncomputable def formsStalkEquiv {S X : Scheme.{u}} (q : X ⟶ S) (n : ℕ) (x : X) :=
  letI := algebraStalkMap q x
  letI := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds x))
  (SheafOfModules.exteriorPowerStalkEquiv
      (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials q))
      (Scheme.Modules.exteriorGenerator _)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n x).trans
    (extCongr n (relativeDifferentialsStalkKaehlerEquiv q x))

/-- **`⋀ⁿ Ω_{K/Λ}` is the generic stalk of `Ω^n_{X/S}`**, for `K` the function field of an
integral scheme `X` and `Λ` the local ring of `S` below the generic point.  This is
`AlgebraicGeometry.formsStalkEquiv` at the generic point, with its scalar ring read as the
function field. -/
noncomputable def genericFormsStalkEquiv {S X : Scheme.{u}} (q : X ⟶ S) [IsIntegral X] (n : ℕ) :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    (⋀[↑X.functionField]^n
        (Ω[↑X.functionField⁄ToType (S.presheaf.stalk (q.base (genericPoint X)))]))
      ≃ₗ[↑X.functionField]
      ↑((Scheme.Hom.relativeDifferentialForms q ((n : ℕ) : ℤ)).presheaf.stalk
        (genericPoint X)) :=
  (formsStalkEquiv q n (genericPoint X)).symm

end AlgebraicGeometry

end
