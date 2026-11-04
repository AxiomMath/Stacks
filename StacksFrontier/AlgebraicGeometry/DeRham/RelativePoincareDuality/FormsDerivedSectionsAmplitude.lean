module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.KunnethTopDegree
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialSpreadOut
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne

/-!
# The amplitude of `RΓ(X, Ωᵖ_{X/A})` for a proper smooth scheme

Let `A` be a Noetherian ring and `f : X ⟶ Spec A` proper and smooth of relative dimension `n`.
Every fibre of `f` has dimension `n`, so the cohomology of a coherent `𝒪_X`-module vanishes above
degree `n` ([Stacks, Tag 02V7]); in particular `RΓ(X, Ωᵖ_{X/A})` lies in degrees `≤ n` in `D(A)`.
This is the amplitude bound under which the top-degree Künneth isomorphism
`AlgebraicGeometry.FlatKunneth.kunnethTopDegreeIso` applies, as it does in the proof of
[Stacks, Tag 0G8J] for `H^{2n}(X ×_A X, Ωᵖ ⊠ Ω^q) = Hⁿ(X, Ωᵖ) ⊗_A Hⁿ(X, Ω^q)`.

## Main results

* `AlgebraicGeometry.TopDegreeDifferential.topologicalKrullDim_fiber_le`: the fibres of a morphism
  smooth of relative dimension `n` have dimension at most `n`.
* `AlgebraicGeometry.TopDegreeDifferential.isLE_sectionsOverBase_forms`: `RΓ(X, Ωᵖ_{X/A}[0])`
  lies in degrees `≤ n`.
* `AlgebraicGeometry.TopDegreeDifferential.formsKunnethTopDegreeIso`:
  `Hⁿ(X, Ωᵖ) ⊗_A Hⁿ(X, Ω^q) ≅ H^{2n}(X ×_A X, Ωᵖ ⊠ Ω^q)`.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase singleD)

universe u

namespace AlgebraicGeometry.TopDegreeDifferential

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The fibres of a morphism smooth of relative dimension `n` have dimension at most `n`.** -/
theorem topologicalKrullDim_fiber_le (n : ℕ) [SmoothOfRelativeDimension n f]
    (s : Spec (.of A)) : topologicalKrullDim (f.fiber s) ≤ (n : WithBot ℕ∞) := by
  have hsmt := smoothOfRelativeDimension_fiberToSpecResidueField f n s
  rcases isEmpty_or_nonempty (f.fiber s) with hE | hN
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hE]
    exact bot_le
  · exact (@topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field _ _ _ hN n _
      hsmt).le

/-- **`RΓ(X, Ωᵖ_{X/A})` lies in degrees `≤ n`** for `f : X ⟶ Spec A` proper and smooth of
relative dimension `n` over a Noetherian ring: the sheaves `Ωᵖ_{X/A}` are coherent, and the
cohomology of a coherent module vanishes above the dimension of the fibres
([Stacks, Tag 02V7]). -/
theorem isLE_sectionsOverBase_forms [IsNoetherianRing A] [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : ℕ) :
    ((sectionsOverBase f.toLRSHom.toShHom).obj
      (singleD (f.relativeDifferentialForms (p : ℤ)))).IsLE n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := Scheme.Hom.isCoherent_relativeDifferentialForms f p
  refine FlatKunneth.isLE_sectionsOverBase_singleD f _ n fun m hm => ?_
  open Stacks.AlgebraicGeometry.FibreDimension in
  exact isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le f
    (topologicalKrullDim_fiber_le f n) _ (by exact_mod_cast hm)

/-- **`Hⁿ(X, Ωᵖ_{X/A}) ⊗_A Hⁿ(X, Ω^q_{X/A}) ≅ H^{2n}(X ×_A X, Ωᵖ ⊠ Ω^q)`** for `f : X ⟶ Spec A`
proper and smooth of relative dimension `n` over a Noetherian ring, all cohomology computed by
`RΓ(-)` in `D(Γ(Spec A, 𝒪))`: the identification of the proof of [Stacks, Tag 0G8J] obtained "by
the Künneth formula … since we are looking in top degree there are no higher tor groups that
intervene". It is `AlgebraicGeometry.FlatKunneth.kunnethTopDegreeIso`, whose hypotheses are the
amplitude bound `AlgebraicGeometry.TopDegreeDifferential.isLE_sectionsOverBase_forms` and the
flatness of the finite locally free `Ω^q_{X/A}` over `A`. -/
def formsKunnethTopDegreeIso [IsNoetherianRing A] [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] (p q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        n).obj ((sectionsOverBase f.toLRSHom.toShHom).obj
          (singleD (f.relativeDifferentialForms (p : ℤ)))) ⊗
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        n).obj ((sectionsOverBase f.toLRSHom.toShHom).obj
          (singleD (f.relativeDifferentialForms (q : ℤ)))) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        ((n : ℤ) + n)).obj
      ((sectionsOverBase (pullback.fst f f ≫ f).toLRSHom.toShHom).obj
        (singleD (externalTensorProduct f f (f.relativeDifferentialForms (p : ℤ))
          (f.relativeDifferentialForms (q : ℤ))))) :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI := isLE_sectionsOverBase_forms f n p
  haveI := isLE_sectionsOverBase_forms f n q
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f q
  haveI := ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f q
  FlatKunneth.kunnethTopDegreeIso f f _ _
    (VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f _) n n

end AlgebraicGeometry.TopDegreeDifferential

end
