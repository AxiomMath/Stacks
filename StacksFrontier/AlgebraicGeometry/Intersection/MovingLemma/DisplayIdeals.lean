module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProductDecomposition
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectionCone
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The two ideal containments of the display of Stacks 0B0E

The local form of Stacks 0B1J which the display `C · X = [Z] + ∑ m_j [Z_j]` goes through takes
two containments of ideals in the local ring of the nonsingular subvariety `X` at the generic
point of `Z`:

* `hker`, that the kernel of `𝒪_{𝐏^N, ξ} ⟶ 𝒪_{X, ξ}` lies in the local ideal of `X` itself — an
  automatic statement, the kernel being the stalk of the ideal sheaf of `X` and the local ideal
  of `X` the stalk of its *reduced* ideal sheaf, which is larger;
* `hπle`, that the ideal `π^{-1}(π(Z))` cuts out on `X` lies in the one `C` cuts out there, which
  is the source's identity `C ∩ X = π^{-1}(π(Z))` in its scheme-theoretic form.

## Main results

* `AlgebraicGeometry.ker_stalkMap_le_localIdealAt`: `hker`, for any closed immersion and any
  point of the support of its ideal sheaf.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.map_stalkMap_localIdealAt_projection_le`: `hπle`,
  for the cone over a closed subset of `𝐏(W)` and a closed subscheme of `𝐏(V)` off the vertex.

## Implementation notes

**`hπle` is an equality composed with a containment, and the containment is the only inequality
in it.** `C` is the closure of the cone, so its reduced ideal sheaf is
`Stacks.IdealSheaf.closureIdeal` of the *reduced* ideal sheaf `I` of `r_W^{-1}(Z)` inside the
domain of definition of `r_W` — both are the vanishing ideal of the same closed set — and
`AlgebraicGeometry.ProjectiveSpaceOfModule.comap_closureIdeal_projection_comp` turns the comap of
that along `j ≫ ι = i_X` into the comap of `I` along `j`, an equality. What remains is that the
comap of the reduced ideal sheaf of `Z` along `r_W` is at most `I`, which is
`Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal`: `I` is the vanishing ideal of the whole
of `r_W^{-1}(Z)` and is therefore the largest ideal sheaf supported there, while the comap is
supported exactly there. Taking `I` reduced is forced — `comap_closureIdeal_projection_comp`
needs it, and the comap of the reduced ideal sheaf of `Z` is not reduced in general — and it is
what makes the remaining step an inequality rather than an equality.

**A lemma that looks applicable but is not.**
`AlgebraicGeometry.TorFormula.map_stalkMap_localIdealAt_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.LocalIdealImage` reads like
`hπle` and is not it: its right-hand side is a local ideal on the *same* scheme as its left-hand
side, which is the shape the ambient form
`AlgebraicGeometry.TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt` consumes. The
display of Stacks 0B0E goes through the closed-subscheme form instead, whose two sides live on
`𝐏^N` and on `X`, because the ambient form's étaleness hypothesis is false in this application —
the projection of `𝐏^N` is an `𝔸^{N-n}`-bundle and étale nowhere.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

universe u

namespace AlgebraicGeometry

/-- **The hypothesis `hker` of the local form of Stacks 0B1J.** The kernel of the map of local
rings induced by a closed immersion `i` at a point `z` is the stalk of the ideal sheaf of `i`,
which is contained in the stalk of the reduced ideal sheaf of the closure of any point of the
support of `i`. -/
public theorem ker_stalkMap_le_localIdealAt {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (z : X) {y : Y} (hy : y ∈ (i.ker.support : Set Y)) :
    RingHom.ker (i.stalkMap z).hom ≤ TorFormula.localIdealAt y (i.base z) := by
  rw [Stacks.Chow.ker_stalkMap_eq_idealStalk_ker i z]
  exact IdealSheafData.stalk_mono
    ((Stacks.Chow.le_integralComponentAt_iff_mem_support i.ker y).mpr hy) _

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The hypothesis `hπle` of the local form of Stacks 0B1J, for the cone of Stacks 0B0E.** Let
`W ≤ V`, let `Zi ⊆ 𝐏(W)` be closed, let `X` be a scheme over `𝐏(V)` whose structure morphism
factors through the domain of definition of `r_W` by `j`, and let `x` be a point of `𝐏(V)` whose
closure is the closure `C` of the cone `r_W^{-1}(Zi)`. Then at every point `ζ` of `X` whose image
under `π = r_W|_X` has closure `Zi`, the ideal that `π^{-1}(Zi)` cuts out on `X` is contained in
the one that `C` cuts out there.

This is the source's `C ∩ X = π^{-1}(π(Z))` in the form the local form of Stacks 0B1J consumes;
see the implementation notes of this module for why only one of the two containments is an
inequality, and for the lemma that looks like this one and is not. -/
public theorem map_stalkMap_localIdealAt_projection_le (W : Submodule k V) {X : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) (j : X ⟶ (projectionDomain k V W).toScheme)
    (hj : j ≫ (projectionDomain k V W).ι = iX)
    {Zi : Set (projectiveSpaceOfModule k ↥W)} (hZcl : IsClosed Zi)
    {x : projectiveSpaceOfModule k V}
    (hx : closure ({x} : Set (projectiveSpaceOfModule k V)) =
      closure (projectionPreimage k V W Zi))
    {ζ : X} (hζ : closure ({(j ≫ projection k V W).base ζ} :
      Set (projectiveSpaceOfModule k ↥W)) = Zi) :
    Ideal.map ((j ≫ projection k V W).stalkMap ζ).hom
        (TorFormula.localIdealAt ((j ≫ projection k V W).base ζ)
          ((j ≫ projection k V W).base ζ)) ≤
      Ideal.map (iX.stalkMap ζ).hom (TorFormula.localIdealAt x (iX.base ζ)) := by
  classical
  -- the reduced ideal sheaf of the cone, read inside the domain of definition of `r_W`
  set I : (projectionDomain k V W).toScheme.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal
      ⟨(projection k V W).base ⁻¹' Zi, hZcl.preimage (projection k V W).continuous⟩ with hIdef
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hIsupp : (I.support : Set (projectionDomain k V W).toScheme) =
      (projection k V W).base ⁻¹' Zi := by
    rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  -- the reduced ideal sheaf of `C` is the closure ideal of `I`
  have hCeq : Stacks.Chow.integralComponentAt x =
      Stacks.IdealSheaf.closureIdeal (projectionDomain k V W).ι I := by
    rw [Stacks.Chow.integralComponentAt, Stacks.IdealSheaf.closureIdeal]
    refine congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext ?_)
    rw [Closeds.coe_closure, Closeds.coe_closure, hIsupp, hx, projectionPreimage]
  rw [← IdealSheafData.stalk_comap, ← IdealSheafData.stalk_comap, hCeq]
  refine IdealSheafData.stalk_mono ?_ ζ
  rw [← hj, comap_closureIdeal_projection_comp k V W j I,
    Scheme.IdealSheafData.comap_comp]
  refine Scheme.IdealSheafData.comap_mono j ?_
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (le_of_eq (Closeds.ext ?_).symm)
  rw [Scheme.IdealSheafData.support_comap]
  change (projection k V W).base ⁻¹'
    ((Stacks.Chow.integralComponentAt ((j ≫ projection k V W).base ζ)).support :
      Set (projectiveSpaceOfModule k ↥W)) = (projection k V W).base ⁻¹' Zi
  rw [Stacks.Chow.coe_support_integralComponentAt, hζ]

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
