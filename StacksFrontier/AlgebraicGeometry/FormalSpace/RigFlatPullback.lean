module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeChartConditionDirections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChangeAdicFiniteType
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined

/-!
# The base change of a rig-flat morphism by a morphism locally of finite type

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GGZ** says that if
`f` is rig-flat (Definition 0GGX) and `g` is locally of finite type (Stacks 0AM4), then the
second projection `X ×_Y Z ⟶ Z` is rig-flat.

## Main results

* `AlgebraicGeometry.FormalSpace.localFiniteTypeReadsOnAffineEtaleDiagrams`: a morphism of
  locally Noetherian formal algebraic spaces which is locally of finite type has every one of
  its chart maps between Noetherian adic rings adic and topologically of finite type.
* `AlgebraicGeometry.FormalSpace.isRigFlat_pullback_snd`: **Stacks 0GGZ**.

## Implementation notes

The proof is the one of the source. Rig-flatness and the property of being adic and
topologically of finite type are local properties of arrows of `WAdm^{Noeth}` (Stacks 0GGU and
Stacks 0GBW), rig-flatness is invariant under isomorphism of source and target
(`Rig.rigFlat_isomorphismInvariant`), and rig-flatness is stable under base change by adic
maps of topologically finite type (Stacks 0GGR,
`AlgebraicGeometry.FormalSpace.rigFlatBaseChangeByAdicFiniteType`). Remark 0GBG
(`AlgebraicGeometry.FormalSpace.conditions_pullback_snd_of_isStableUnderBaseChangeBy`) then
carries condition (1) of Stacks 0ANG from `f` and from `g` to the second projection, and that
condition is rig-flatness by Definition 0GGX.

The chart condition Remark 0GBG asks of `g` is drawn from local finite type as in the
discussion of Section 0AQ2: by Stacks 0ANW every chart map of `g` is taut and topologically of
finite type, and a taut homomorphism out of a ring with a finitely generated ideal of
definition — as a Noetherian adic ring has — is adic (Stacks 0GBS).

## References

* [Stacks Project, Tag 0GGZ](https://stacks.math.columbia.edu/tag/0GGZ)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGU](https://stacks.math.columbia.edu/tag/0GGU)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart maps of a morphism locally of finite type, over `WAdm^{Noeth}`.** A morphism of
locally Noetherian formal algebraic spaces over `S` which is locally of finite type has every
chart map between formal spectra of Noetherian adic rings induced by a continuous homomorphism
which is adic and topologically of finite type: Stacks 0ANW makes it taut and topologically of
finite type, and tautness out of a Noetherian adic ring is adicness. -/
theorem localFiniteTypeReadsOnAffineEtaleDiagrams :
    LocalFiniteTypeReadsOnAffineEtaleDiagrams B S hS := by
  intro X Y g _hX _hY hg U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV φ hφ
  have hR : TopologicalRing.IsWeaklyAdmissible R := hCR.1.isWeaklyAdmissible
  have h1 :=
    hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType g hg
  obtain ⟨htaut, hft⟩ := h1 U V a b t hU hV ha hb hsq A R
    ⟨hA, Rig.countablyGenerated_nhds_of_isAdicRing hCA.1⟩
    ⟨hR, Rig.countablyGenerated_nhds_of_isAdicRing hCR.1⟩ hA D E eU eV φ hφ
  obtain ⟨I, -, hI⟩ := hCA.1.1
  have : IsNoetherianRing A := hCA.2
  exact ⟨@RingHom.isAdic_of_isTaut A R _ _ _ _ _ _ _ _ φ.toRingHom φ.continuous htaut
    ⟨I, IsNoetherian.noetherian I, hI⟩ hR.2.1 hR.2.2, hft⟩

/-- **Stacks 0GGZ.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` is rig-flat and `g` is locally of finite type, then the base
change `X ×_Y Z ⟶ Z` is rig-flat. -/
@[stacks 0GGZ]
theorem isRigFlat_pullback_snd {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hf : IsRigFlat B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) :
    IsRigFlat B S hS (pullback.snd f g) :=
  (isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram (pullback.snd f g)).mpr
    (conditions_pullback_snd_of_isStableUnderBaseChangeBy B S hS _ _
      (rigFlat_isStableUnderBaseChangeByAdicFiniteType rigFlatBaseChangeByAdicFiniteType)
      Rig.rigFlat_isomorphismInvariant f g hX hY hZ
      ((isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram f).mp hf)
      (localFiniteTypeReadsOnAffineEtaleDiagrams B S hS g hZ hY hg)).1

end AlgebraicGeometry.FormalSpace

end
