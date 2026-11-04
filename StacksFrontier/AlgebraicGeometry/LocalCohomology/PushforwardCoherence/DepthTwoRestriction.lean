module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic

/-!
# Coherence of the direct image of a restriction of depth at least two

Let `X` be a locally Noetherian scheme, `U ⊆ X` an open with complement `Z`, `j : U ⟶ X` the
inclusion, and `G` a coherent `𝒪_X`-module whose stalk at every point of `Z` has depth at least
two. Then `j_*(G|_U)` is coherent, and so is every quasi-coherent submodule of it.

## Main results

* `Stacks.LocalCohomology.isCoherent_pushforward_pullback_of_two_le_depth_of_notMem`: the direct
  image of the pullback of `G` to `U` is coherent.
* `Stacks.LocalCohomology.isCoherent_pushforward_restrict_of_two_le_depth_of_notMem`: the same for
  the restriction `G|_U`.
* `Stacks.LocalCohomology.isCoherent_of_mono_pushforward_restrict_of_two_le_depth_of_notMem`: a
  quasi-coherent module admitting an injection into `j_*(G|_U)` is coherent.

## References

* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.LocalCohomology

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Let `X` be a locally Noetherian scheme, `U ⊆ X` an open and `G` a coherent `𝒪_X`-module whose
stalk has depth at least two at every point outside `U`. Then the direct image along `U ⟶ X` of
the pullback of `G` to `U` is coherent. -/
theorem isCoherent_pushforward_pullback_of_two_le_depth_of_notMem (G : X.Modules) [G.IsCoherent]
    (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj G)).IsCoherent := by
  have hunit := AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X G U hdepth
  have : ((𝟭 X.Modules).obj G).IsCoherent := by simpa using (inferInstance : G.IsCoherent)
  have hcomp :
      ((Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pushforward U.ι).obj G).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G)).symm
  simpa using hcomp

/-- Let `X` be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open, and `G` a
coherent `𝒪_X`-module whose stalk has depth at least two at every point outside `U`. Then
`j_*(G|_U)` is coherent. -/
theorem isCoherent_pushforward_restrict_of_two_le_depth_of_notMem (G : X.Modules) [G.IsCoherent]
    (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    ((Scheme.Modules.pushforward U.ι).obj (G.restrict U.ι)).IsCoherent :=
  have : ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj G)).IsCoherent :=
    isCoherent_pushforward_pullback_of_two_le_depth_of_notMem G U hdepth
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((Scheme.Modules.pushforward U.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app G))

/-- Let `X` be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open, and `G` a
coherent `𝒪_X`-module whose stalk has depth at least two at every point outside `U`. Then any
quasi-coherent `𝒪_X`-module admitting an injection into `j_*(G|_U)` is coherent. -/
theorem isCoherent_of_mono_pushforward_restrict_of_two_le_depth_of_notMem (G : X.Modules)
    [G.IsCoherent] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))
    (H : X.Modules) [H.IsQuasicoherent]
    (ι : H ⟶ (Scheme.Modules.pushforward U.ι).obj (G.restrict U.ι)) [Mono ι] :
    H.IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent
    (isCoherent_pushforward_restrict_of_two_le_depth_of_notMem G U hdepth) ι

end Stacks.LocalCohomology

end
