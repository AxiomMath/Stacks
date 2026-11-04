module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeTor
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineDictionaryNatural
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentUnion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectUnion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentSituationIso

/-!
# Relatively perfect objects along a relative descent situation

In the relative descent situation of Stacks 0DI6 — a directed inverse limit `S = lim Sᵢ` of
quasi-compact, quasi-separated schemes with affine transition maps, and a flat morphism of finite
presentation `X₀ ⟶ S₀` with base changes `Xᵢ ⟶ Sᵢ` and `X ⟶ S` — this file proves Stacks 0DI7 and
Stacks 0DI8.

Stacks 0DI7: for `K₀` pseudo-coherent and `L₀` in `D_QCoh(𝒪_{X₀})` of locally finite Tor
dimension over `(X₀ ⟶ S₀)⁻¹𝒪_{S₀}`,
`colim_i Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)` is bijective.
The proof is the induction of Stacks 08DR over the quasi-compact opens of `X₀`, run on the shifts
of `K₀`: the affine case over an affine open of `S₀` is Stacks 0DHX read through the natural
affine dictionary, and the union step is the Mayer--Vietoris triangle of Stacks 08BU.

Stacks 0DI8: the category of `S`-perfect objects of `D(𝒪_X)` is the colimit of the categories of
`Sᵢ`-perfect objects of `D(𝒪_{Xᵢ})`. The transition functors `Lf_{ji}^*` and the comparison
functors `Lfᵢ^*` preserve relative perfectness (Stacks 0DI5); the comparison out of the colimit is
fully faithful by Stacks 0DI7, applied to the situation reindexed at the stage of the two objects;
and it is essentially surjective by the induction of Stacks 08DR, whose union step glues along an
overlap isomorphism descended to a stage by that full faithfulness.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_projection`: the derived
  pullback to the limit of an `Sᵢ`-perfect object is `S`-perfect.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_of_isPseudoCoherent`: **Stacks 0DI7.**
* `AlgebraicGeometry.RelativeDescentSituation.homDescentAt_of_isPerfectAt`: full faithfulness of
  the comparison out of the colimit of the categories of relatively perfect objects.
* `AlgebraicGeometry.RelativeDescentSituation.perfectEssentiallySurjectiveCanonical`: its
  essential surjectivity.
* `AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_colimit`: **Stacks 0DI8.**

## Implementation notes

The colimit of the categories `D_{Sᵢ-perf}(𝒪_{Xᵢ})` along the functors `Lf_{ji}^*` has as objects
the pairs `(i, Eᵢ)`, and as morphisms from `(i, Kᵢ)` to `(i, Lᵢ)` the colimit over `j ≥ i` of
`Hom_{D(𝒪_{Xⱼ})}(Lf_{ji}^*Kᵢ, Lf_{ji}^*Lᵢ)` (two objects at different stages being compared at a
common later stage). The assertion that `D_{S-perf}(𝒪_X)` is that colimit is therefore the
conjunction stated in `isPerfectRelativeTo_colimit`: the functors preserve relative perfectness,
the comparison on morphism sets is bijective
(`AlgebraicGeometry.RelativeDescentSituation.HomDescentAt`), and every `S`-perfect object is
`Lfᵢ^*Eᵢ` for some stage `i` and some `Sᵢ`-perfect `Eᵢ`. Relative perfectness is read at the
canonical derived-tensoring certificates throughout.

The Tor-dimension hypothesis of Stacks 0DI7 is the second clause of Stacks 0DI0 for `L₀`, the
source's "(locally) finite tor dimension as an object of `D((X₀ → S₀)⁻¹𝒪_{S₀})`".

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Situation 36.35.7 (Tag 0DI6)](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Lemma 36.35.8 (Tag 0DI7)](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- The limit `X = S ×_{S₀} X₀` as the base change of the stage `Xᵢ` along `S ⟶ Sᵢ`. -/
def limitIsoPullback (i : D.LaterIndex) :
    pullback (D.structureMapAt i) (D.descent.limitCone.π.app (op i.1)) ≅ D.limitScheme :=
  pullbackLeftPullbackSndIso D.X₀.hom (D.baseMap i) (D.descent.limitCone.π.app (op i.1)) ≪≫
    pullback.congrHom rfl (D.descent.limitCone.w (homOfLE i.2).op)

/-- Under `limitIsoPullback`, the structure morphism `X ⟶ S` of the limit is the second projection
of the pullback. -/
theorem limitIsoPullback_hom_structureMapLimit (i : D.LaterIndex) :
    (D.limitIsoPullback i).hom ≫ D.structureMapLimit =
      pullback.snd (D.structureMapAt i) (D.descent.limitCone.π.app (op i.1)) := by
  dsimp only [limitIsoPullback, Iso.trans_hom, pullback.congrHom, asIso_hom, structureMapLimit]
  rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- Under `limitIsoPullback`, the projection `X ⟶ Xᵢ` from the limit is the first projection of
the pullback. -/
theorem limitIsoPullback_hom_projection (i : D.LaterIndex) :
    (D.limitIsoPullback i).hom ≫ D.projection i =
      pullback.fst (D.structureMapAt i) (D.descent.limitCone.π.app (op i.1)) := by
  dsimp only [limitIsoPullback, Iso.trans_hom, pullback.congrHom, asIso_hom, projection,
    structureMapAt]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc]
    exact pullback.condition.symm

/-- The structure morphism of the limit, as the base change of that of `Xᵢ`. -/
def structureMapLimitArrowIso (i : D.LaterIndex) :
    Scheme.Hom.ringedArrow
        (pullback.snd (D.structureMapAt i) (D.descent.limitCone.π.app (op i.1))) ≅
      Scheme.Hom.ringedArrow D.structureMapLimit :=
  Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso (D.limitIsoPullback i)) (Iso.refl _)
    ((Scheme.forgetToRingedSpace.map_comp _ _).symm.trans
      ((congrArg Scheme.forgetToRingedSpace.map (D.limitIsoPullback_hom_structureMapLimit i)).trans
        (Category.comp_id _).symm))

/-- **The derived pullback to the limit preserves relative perfectness.** For an object `E` of
`D(𝒪_{Xᵢ})` perfect relative to `Sᵢ`, the derived pullback of `E` along `X ⟶ Xᵢ` is perfect
relative to `S`. -/
theorem isPerfectRelativeTo_projection (i : D.LaterIndex)
    (E : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace))
    (hE : letI : Flat D.X₀.hom := D.flat
      letI : LocallyOfFinitePresentation D.X₀.hom :=
        D.finitePresentation.locallyOfFinitePresentation
      (D.structureMapAt i).IsPerfectRelativeTo (D.canonicalStageCertificates i) E) :
    letI : Flat D.X₀.hom := D.flat
    letI : LocallyOfFinitePresentation D.X₀.hom :=
      D.finitePresentation.locallyOfFinitePresentation
    D.structureMapLimit.IsPerfectRelativeTo D.canonicalLimitCertificates
      ((derivedPullback (D.projection i).toLRSHom.toShHom).obj E) := by
  let : Flat D.X₀.hom := D.flat
  let : LocallyOfFinitePresentation D.X₀.hom :=
    D.finitePresentation.locallyOfFinitePresentation
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace
      (pullback (D.structureMapAt i) (D.descent.limitCone.π.app (op i.1))).carrier := by
    have := D.compactSpace_limitScheme
    exact (D.limitIsoPullback i).hom.homeomorph.symm.compactSpace
  refine (Scheme.Hom.isPerfectRelativeTo_arrowIso_iff _ _ (D.structureMapLimitArrowIso i) _).1 ?_
  refine Scheme.Hom.isPerfectRelativeTo_canonical_of_iso _ ?_
    (Scheme.Hom.isPerfectRelativeTo_derivedPullback_pullbackFst (D.structureMapAt i)
      (D.descent.limitCone.π.app (op i.1)) E hE)
  exact ((Stacks.DerivedPullback.schemeFactorIso (D.limitIsoPullback i).hom (D.projection i)
    _ (D.limitIsoPullback_hom_projection i)).app E).symm

/-! ### Stacks 0DI7 -/

/-- The Tor-dimension clause of Stacks 0DI0 for `X₀ ⟶ S₀` passes to an affine open `V₀ ⊆ X₀`
lying over an open `W₀ ⊆ S₀`, read over `V₀ ⟶ W₀`. -/
theorem locallyHasFiniteTorDimension_resLE
    (W₀ : (D.descent.system.obj (op D.descent.base)).Opens) (V₀ : D.X₀.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
    (L₀ : DerivedCategory (OXMod.{u, u} D.X₀.left.toRingedSpace))
    (h : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage (D.descent.system.obj (op D.descent.base)).toRingedSpace
        D.X₀.hom.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction D.X₀.hom).obj L₀)) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage W₀.toScheme.toRingedSpace (D.X₀.hom.resLE W₀ V₀ hVW).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction (D.X₀.hom.resLE W₀ V₀ hVW)).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)) := by
  have : CompactSpace V₀.toScheme := isCompact_iff_compactSpace.mp hV₀.isCompact
  exact (Scheme.Hom.locallyHasFiniteTorDimension_baseOpen_iff (D.X₀.hom.resLE W₀ V₀ hVW) W₀.ι
    (Scheme.Hom.resLE_comp_ι _ _) _).1
    (Scheme.Hom.locallyHasFiniteTorDimension_torClause_comp_openImmersion D.X₀.hom V₀.ι L₀ h)

/-- **Stacks 0DI7.** In Situation 0DI6, let `K₀` and `L₀` be objects of `D(𝒪_{X₀})` with `K₀`
pseudo-coherent and `L₀` in `D_QCoh(𝒪_{X₀})` of locally finite Tor dimension as an object of
`D((X₀ ⟶ S₀)⁻¹𝒪_{S₀})`. Then
`colim_i Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`
is bijective. -/
theorem homDescent_of_isPseudoCoherent
    (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀tor : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage (D.descent.system.obj (op D.descent.base)).toRingedSpace
        D.X₀.hom.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction D.X₀.hom).obj L₀)) :
    D.HomDescent K₀ L₀ :=
  D.homDescent_of_restrictHomDescent_shift_isAffineOpenOverAffine K₀ L₀
    fun V₀ hV₀ ⟨W₀, hW₀, hVW⟩ n =>
      D.restrictHomDescent_of_isAffineOpen_resLE W₀ V₀ hV₀ hVW hW₀ (K₀⟦n⟧) L₀ (hK₀.shift n)
        hL₀qc (D.locallyHasFiniteTorDimension_resLE W₀ V₀ hV₀ hVW L₀ hL₀tor)

/-! ### Stacks 0DI8 -/

/-- **Full faithfulness of the comparison out of the colimit of the categories of relatively
perfect objects.** For `Sᵢ`-perfect objects `K` and `L` of `D(𝒪_{Xᵢ})`,
`colim_{j ≥ i} Hom_{D(𝒪_{Xⱼ})}(Lf_{ji}^*K, Lf_{ji}^*L) ⟶ Hom_{D(𝒪_X)}(Lfᵢ^*K, Lfᵢ^*L)` is
bijective. This is Stacks 0DI7 for the situation reindexed at the stage `i`. -/
theorem homDescentAt_of_isPerfectAt (i : D.LaterIndex)
    (K L : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace))
    (hK : D.IsPerfectAt i K) (hL : D.IsPerfectAt i L) : D.HomDescentAt i K L :=
  D.homDescentAt_of_reindex i K L ((D.reindex i).homDescent_of_isPseudoCoherent K L hK.1
    (isQuasicoherentDerived_of_isPseudoCoherent (D.schemeAt i) L hL.1) hL.2)

/-- **Essential surjectivity of the comparison out of the colimit of the categories of
relatively perfect objects.** Every `S`-perfect object of `D(𝒪_X)` is the derived pullback, from
some stage `i`, of an `Sᵢ`-perfect object of `D(𝒪_{Xᵢ})`. -/
theorem perfectEssentiallySurjectiveCanonical : D.PerfectEssentiallySurjectiveCanonical :=
  D.perfectEssentiallySurjectiveCanonical_of_fullyFaithful
    fun D' => D'.homDescentAt_of_isPerfectAt

/-- **Stacks 0DI8.** In Situation 0DI6 the category of `S`-perfect objects of `D(𝒪_X)` is the
colimit of the categories of `Sᵢ`-perfect objects of `D(𝒪_{Xᵢ})`: the transition functors
`Lf_{ji}^*` and the comparison functors `Lfᵢ^*` carry relatively perfect objects to relatively
perfect objects, the comparison out of the colimit is fully faithful, and it is essentially
surjective. -/
@[stacks 0DI8]
theorem isPerfectRelativeTo_colimit :
    (∀ {i j : D.LaterIndex} (h : i.1 ≤ j.1)
        (E : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace)),
        D.IsPerfectAt i E →
          D.IsPerfectAt j ((derivedPullback (D.transition h).toLRSHom.toShHom).obj E)) ∧
      (∀ (i : D.LaterIndex) (E : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace)),
        D.IsPerfectAt i E →
          letI : Flat D.X₀.hom := D.flat
          letI : LocallyOfFinitePresentation D.X₀.hom :=
            D.finitePresentation.locallyOfFinitePresentation
          D.structureMapLimit.IsPerfectRelativeTo D.canonicalLimitCertificates
            ((derivedPullback (D.projection i).toLRSHom.toShHom).obj E)) ∧
      (∀ (i : D.LaterIndex) (K L : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace)),
        D.IsPerfectAt i K → D.IsPerfectAt i L → D.HomDescentAt i K L) ∧
      D.PerfectEssentiallySurjectiveCanonical :=
  ⟨D.isPerfectRelativeTo_transition,
    fun i E hE => D.isPerfectRelativeTo_projection i E hE,
    D.homDescentAt_of_isPerfectAt,
    D.perfectEssentiallySurjectiveCanonical⟩

end AlgebraicGeometry.RelativeDescentSituation

end
