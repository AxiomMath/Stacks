module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafKer
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalUniversal

/-!
# The defining ideal sheaf of an infinitesimal neighbourhood is `I/Iⁿ⁺¹`

Let `i : Z ⟶ X` be an immersion of schemes, with closed-immersion factorization
`AlgebraicGeometry.Scheme.Hom.liftCoborder` into the canonical open neighbourhood
`AlgebraicGeometry.Scheme.Hom.coborderRange` of its image, and let `K` be the defining ideal sheaf
of that factorization. The `n`th-order infinitesimal neighbourhood `Zₙ` is cut out by
`K ^ (n + 1)`. Over an affine open `V` of the ambient open subscheme, the defining ideal sheaf of
the inclusion `Z ⟶ Zₙ` is the image of `K(V)` in `Γ(V) ⧸ K(V) ^ (n + 1)`, i.e. `I/Iⁿ⁺¹`, and for
`n = 1` it is `I/I²`. This holds both for the ideal-sheaf datum
`AlgebraicGeometry.Scheme.Hom.ker` and for the sheaf of modules `Stacks.ClosedImmersion.idealSheaf`
on the underlying ringed space.

## Main results

* `Stacks.Thickenings.ker_app_nthOrderι` computes the chart maps of an infinitesimal
  neighbourhood: the kernel of `Γ(V) ⟶ Γ(Zₙ, Zₙ ∩ V)` is `K(V) ^ (n + 1)`.
* `Stacks.Thickenings.ker_ideal_nthOrderInclusion` is the computation of the defining ideal sheaf
  of the inclusion `Z ⟶ Zₙ` as an ideal-sheaf datum, and
  `Stacks.Thickenings.ker_app_nthOrderInclusion` the same as the kernel of a map on sections.
* `Stacks.Thickenings.range_idealSheafι_val_app_nthOrderInclusion` is the same computation for the
  ringed-space ideal sheaf `Stacks.ClosedImmersion.idealSheaf`: its sections over a chart of `Zₙ`
  land in `Γ(Zₙ, Zₙ ∩ V)` as the image of `K(V)`.
* `Stacks.Thickenings.range_idealSheafι_val_app_firstOrder` and
  `Stacks.Thickenings.ker_app_firstOrderι` are the pair of statements at `n = 1` that exhibit
  that ideal sheaf as `I/I²`: its sections are the image of `K(V)` under a surjection whose kernel
  is `K(V) ^ 2`.
* `Stacks.ClosedImmersion.isIso_conormalSheafMap_iff` and
  `Stacks.Thickenings.isIso_infinitesimalConormalSheafMap_iff` reduce the invertibility of the
  ringed-space comparison `Stacks.Thickenings.infinitesimalConormalSheafMap` to that of the
  pullback along `Z ⟶ Z₁` of `Stacks.ClosedImmersion.idealSheafMap`.

## Implementation notes

The inclusion `Z ⟶ Zₙ` is not an `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` but
`AlgebraicGeometry.IsClosedImmersion.lift` of the factorization of `i` through the subscheme cut
out by `K ^ (n + 1)`, so the computation goes through `Stacks.ClosedImmersion.ker_ideal_preimage`
and the surjectivity of the chart map.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
* [Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- The conormal-sheaf map of a commutative square is invertible if and only if the pullback
along `i` of its ideal-sheaf map `Stacks.ClosedImmersion.idealSheafMap` is. -/
theorem isIso_conormalSheafMap_iff {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f : Z ⟶ W} {k : Z' ⟶ W'} (comm : i ≫ k = f ≫ j) :
    IsIso (conormalSheafMap comm) ↔ IsIso ((modulePullback i).map (idealSheafMap comm)) :=
  isIso_comp_left_iff _ _

end Stacks.ClosedImmersion

namespace Stacks.Thickenings

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-! ### The chart maps of an infinitesimal neighbourhood -/

/-- The chart `Γ(V) ⟶ Γ(Zₙ, Zₙ ∩ V)` of the `n`th-order infinitesimal neighbourhood over an
affine open `V` of the ambient open subscheme has `K(V) ^ (n + 1)` as its kernel, for `K` the
defining ideal sheaf of the closed-immersion factorization of `i`. -/
theorem ker_app_nthOrderι (n : ℕ) (V : i.coborderRange.toScheme.affineOpens) :
    RingHom.ker ((nthOrderι i n).app V.1).hom = i.liftCoborder.ker.ideal V ^ (n + 1) :=
  ((i.liftCoborder.ker ^ (n + 1)).ker_subschemeι_app V).trans
    (congrFun (Scheme.IdealSheafData.ideal_pow (I := i.liftCoborder.ker) (n + 1)) V)

/-- The chart of the first-order infinitesimal neighbourhood over an affine open `V` has
`K(V) ^ 2` as its kernel. -/
theorem ker_app_firstOrderι (V : i.coborderRange.toScheme.affineOpens) :
    RingHom.ker ((nthOrderι i 1).app V.1).hom = i.liftCoborder.ker.ideal V ^ 2 :=
  ker_app_nthOrderι i 1 V

/-! ### The defining ideal sheaf of the inclusion -/

/-- On the chart `nthOrderι i n ⁻¹ᵁ V` of the `n`th-order infinitesimal neighbourhood over an
affine open `V` of the ambient open subscheme, the ideal that `AlgebraicGeometry.Scheme.Hom.ker`
assigns to the inclusion `Z ⟶ Zₙ` is the image of `K(V)` under the chart map, for `K` the defining
ideal sheaf of the closed-immersion factorization of `i`. -/
theorem ker_ideal_nthOrderInclusion (n : ℕ) (V : i.coborderRange.toScheme.affineOpens) :
    (nthOrderInclusion i n).ker.ideal ⟨nthOrderι i n ⁻¹ᵁ V.1, V.2.preimage _⟩ =
      Ideal.map ((nthOrderι i n).app V.1).hom (i.liftCoborder.ker.ideal V) := by
  rw [Stacks.ClosedImmersion.ker_ideal_preimage _ (nthOrderι i n) V _
    ((i.liftCoborder.ker ^ (n + 1)).subschemeι_app_surjective V), nthOrderInclusion_nthOrderι]

/-- The section map of the inclusion `Z ⟶ Zₙ` over the chart `nthOrderι i n ⁻¹ᵁ V` has the
image of `K(V)` under the chart map as its kernel. -/
theorem ker_app_nthOrderInclusion (n : ℕ) (V : i.coborderRange.toScheme.affineOpens) :
    RingHom.ker ((nthOrderInclusion i n).app (nthOrderι i n ⁻¹ᵁ V.1)).hom =
      Ideal.map ((nthOrderι i n).app V.1).hom (i.liftCoborder.ker.ideal V) :=
  (Scheme.Hom.ker_apply (nthOrderInclusion i n)
    ⟨nthOrderι i n ⁻¹ᵁ V.1, V.2.preimage _⟩).symm.trans (ker_ideal_nthOrderInclusion i n V)

/-! ### The ringed-space ideal sheaf of the inclusion -/

/-- The sections over the chart `nthOrderι i n ⁻¹ᵁ V` of the sheaf of modules
`Stacks.ClosedImmersion.idealSheaf` of the inclusion `Z ⟶ Zₙ` land in `Γ(Zₙ, Zₙ ∩ V)` as the image
of `K(V)` under the chart map. -/
theorem range_idealSheafι_val_app_nthOrderInclusion (n : ℕ)
    (V : i.coborderRange.toScheme.affineOpens) :
    LinearMap.range ((Stacks.ClosedImmersion.idealSheafι
          (nthOrderInclusion i n).toLRSHom.toShHom).val.app (op (nthOrderι i n ⁻¹ᵁ V.1))).hom =
      Ideal.map ((nthOrderι i n).app V.1).hom (i.liftCoborder.ker.ideal V) :=
  (Stacks.ClosedImmersion.range_idealSheafι_val_app_eq_ker_ideal (nthOrderInclusion i n)
    ⟨nthOrderι i n ⁻¹ᵁ V.1, V.2.preimage _⟩).trans (ker_ideal_nthOrderInclusion i n V)

/-- Over an affine open `V` of the ambient open subscheme, the sections of
`Stacks.ClosedImmersion.idealSheaf (nthOrderInclusion i 1)` land in `Γ(Z₁, Z₁ ∩ V)` as the image
of `K(V)` under the chart map, the quotient by `K(V) ^ 2`; so they are `K(V)/K(V)²`. -/
theorem range_idealSheafι_val_app_firstOrder (V : i.coborderRange.toScheme.affineOpens) :
    LinearMap.range ((Stacks.ClosedImmersion.idealSheafι
          (nthOrderInclusion i 1).toLRSHom.toShHom).val.app (op (nthOrderι i 1 ⁻¹ᵁ V.1))).hom =
      Ideal.map ((nthOrderι i 1).app V.1).hom (i.liftCoborder.ker.ideal V) :=
  range_idealSheafι_val_app_nthOrderInclusion i 1 V

/-! ### The ringed-space conormal comparison -/

/-- The comparison morphism `Stacks.Thickenings.infinitesimalConormalSheafMap` of an immersion is
an isomorphism if and only if the pullback along the inclusion `Z ⟶ Z₁` of the ideal-sheaf
comparison `Stacks.ClosedImmersion.idealSheafMap` of the square
`Stacks.Thickenings.toShHom_nthOrderInclusion_nthOrderι` is. -/
theorem isIso_infinitesimalConormalSheafMap_iff :
    IsIso (infinitesimalConormalSheafMap i) ↔
      IsIso ((modulePullback (nthOrderInclusion i 1).toLRSHom.toShHom).map
        (Stacks.ClosedImmersion.idealSheafMap (toShHom_nthOrderInclusion_nthOrderι i))) :=
  Stacks.ClosedImmersion.isIso_conormalSheafMap_iff _

end Stacks.Thickenings

end
