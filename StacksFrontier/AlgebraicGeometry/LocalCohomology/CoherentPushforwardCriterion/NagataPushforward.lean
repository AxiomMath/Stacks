module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Serre

/-!
# Coherence of a direct image across a complement of depth at least two

Let `X` be a locally Noetherian scheme and `U ⊆ X` an open subscheme with complement `Z`. A
coherent `𝒪_X`-module whose stalks along `Z` have depth at least two is the direct image of its
own restriction to `U`; consequently that direct image is coherent, and so is the direct image
of any quasi-coherent `𝒪_U`-module that embeds into the restriction.

## Main results

* `AlgebraicGeometry.isCoherent_pushforward_pullback_of_depth_ge_two`: for `G` coherent on `X`
  with depth at least two along the complement of `U`, the module `j_*(G|_U)` is coherent.
* `AlgebraicGeometry.isCoherent_pushforward_of_mono_of_depth_ge_two`: a quasi-coherent
  `𝒪_U`-module admitting a monomorphism into `G|_U` has coherent direct image.
* `AlgebraicGeometry.two_le_depth_stalk_of_isNormal_of_two_le_ringKrullDim`: on a normal locally
  Noetherian scheme a local ring of dimension at least two has depth at least two.

## Implementation notes

Restriction to `U` is pullback along `U.ι`, and the comparison map `G ⟶ j_*(G|_U)` is the unit
of the pullback--pushforward adjunction, matching the form in which the Hartogs extension
theorem [Stacks, Tag 0E9I] is stated. `AlgebraicGeometry.HasDepthTwoOutside` names the depth
hypothesis of that theorem so that the three statements below can share it verbatim.

Coherence is transported across the unit isomorphism through
`Stacks.SheafOfModules.coherentModules`, which is closed under isomorphisms; the two spellings
of the coherence predicate are interchanged by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'` and its converse.

The monomorphism statement reduces to the previous one by [Stacks, Tag 01Y1]: a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme is coherent. Direct image
preserves monomorphisms because it is a right adjoint, hence preserves pullbacks.

The depth bound is Serre's criterion [Stacks, Tag 0345] in the direction that reads off
condition `(S₂)` from normality; it is stated positively, as a lower bound on depth given a
lower bound on dimension, which is the form in which the argument of [Stacks, Tag 0AWA] uses
it.

## References

* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The stalk of a sheaf of modules has depth at least two at every point outside an open
subscheme. This is the hypothesis of the Hartogs extension theorem
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`. -/
public abbrev HasDepthTwoOutside (X : Scheme.{u}) (G : X.Modules) (U : X.Opens) : Prop :=
  ∀ z : X, z ∉ (U : Set X) →
    letI : Module (X.presheaf.stalk z)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf z) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        G.val z
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk z)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf z)

/-- The direct image of the restriction of a coherent module to an open subscheme is coherent,
provided the stalks of the module have depth at least two along the complement: the module is
then carried isomorphically onto that direct image by the unit of the adjunction. -/
public theorem isCoherent_pushforward_pullback_of_depth_ge_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (G : X.Modules) [G.IsCoherent] (U : X.Opens)
    (hdepth : HasDepthTwoOutside X G U) :
    ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj G)).IsCoherent := by
  have h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two X G U hdepth
  have hG : Stacks.SheafOfModules.coherentModules X.ringCatSheaf ((𝟭 X.Modules).obj G) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent ‹G.IsCoherent›
  have hres := ObjectProperty.prop_of_iso (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    (@asIso _ _ _ _ _ h) hG
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent' hres

/-- The direct image of a quasi-coherent module on an open subscheme is coherent as soon as the
module embeds into the restriction of a coherent module whose stalks have depth at least two
along the complement: the direct image is then a quasi-coherent submodule of a coherent
module. -/
public theorem isCoherent_pushforward_of_mono_of_depth_ge_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (G : X.Modules) [G.IsCoherent] (hdepth : HasDepthTwoOutside X G U)
    (F : U.toScheme.Modules) [F.IsQuasicoherent]
    (φ : F ⟶ (Scheme.Modules.pullback U.ι).obj G) [Mono φ] :
    ((Scheme.Modules.pushforward U.ι).obj F).IsCoherent := by
  have hcoh := isCoherent_pushforward_pullback_of_depth_ge_two X G U hdepth
  have hpl : Limits.PreservesLimitsOfSize.{u, u} (Scheme.Modules.pushforward U.ι) :=
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).rightAdjoint_preservesLimits
  have hmono : Mono ((Scheme.Modules.pushforward U.ι).map φ) :=
    preserves_mono_of_preservesLimit _ φ
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
    ((Scheme.Modules.pushforward U.ι).map φ)

/-- A local ring of a normal locally Noetherian scheme whose dimension is at least two has depth
at least two, by Serre's condition `(S₂)`. -/
@[ega "IV 5.8.6" "necessity of clause (ii)",
  ega "IV 7.3.9" "(i)",
  sga "2 XI 3.11" "necessity: (ii)"]
public theorem two_le_depth_stalk_of_isNormal_of_two_le_ringKrullDim
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (hY : IsNormal Y) (y : Y)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)) :
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) := by
  have hS2 := ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one Y).mp hY).1 y
  have hdim' : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y) := by
    exact_mod_cast hdim
  have hcast : ((2 : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := rfl
  rw [min_eq_left hdim', ← hcast, WithBot.coe_le_coe] at hS2
  exact hS2

end AlgebraicGeometry

end
