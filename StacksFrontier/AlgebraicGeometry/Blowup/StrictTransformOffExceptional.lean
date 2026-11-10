module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
import StacksFrontier.AlgebraicGeometry.IteratedBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# The strict transform is the base change away from the exceptional divisor

Let `f : X ⟶ S` be a morphism of schemes and `ℐ` a quasi-coherent sheaf of ideals on `S`, with
blowup `b : S' ⟶ S` and exceptional divisor `E`. The strict transform `X' ⊆ X ×_S S'` is the
closed subscheme cut out by the sections of the structure sheaf supported on `pr_{S'}⁻¹ E`
(Stacks tag 080D). This file proves that the closed immersion `X' ⟶ X ×_S S'` is an
**isomorphism over the complement of `pr_{S'}⁻¹ E`**: away from the exceptional divisor the
strict transform of `f` is the plain base change of `f`.

The repository had this at the level of modules —
`Stacks.StrictTransform.isIso_restrictFunctor_map_π` says the quotient map onto the strict
transform of a module becomes an isomorphism over that open — but not at the level of schemes,
and that is what both consumers below need.

## Main results

* `Stacks.StrictTransform.isIso_subschemeι_restrict` and
  `Stacks.Blowup.isIso_strictTransformι_restrict`: **the identification**, for the strict
  transform along an arbitrary morphism and ideal sheaf and for the strict transform along a
  blowup respectively. Both are also registered as instances at the complement itself.
* `Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_restrict`: the first consumer.
  Over an open of the blowup disjoint from the exceptional divisor the strict transform is
  locally of finite presentation, because there it is a base change of `f`.
* `Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat_of_dense` and
  `Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat`: so a strict transform
  which is flat over the blowup is locally of finite presentation over it, by Stacks tag 081P —
  with no further hypothesis, the complement of the exceptional divisor being retrocompact
  (`Stacks.Blowup.isRetrocompact_compl_support_exceptionalIdeal`) and scheme-theoretically dense
  (`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`). This is the
  locally-of-finite-presentation half of Stacks tag 0815, granted its flatness half.
* `Stacks.Blowup.exists_unique_lift_strictTransformι`: the second consumer. A morphism to
  `X ×_S S'` which, after restriction along a scheme-theoretically dominant morphism, lands in
  the complement of `pr_{S'}⁻¹ E` factors uniquely through the strict transform.

## Implementation notes

The engine is not the module-level statement but
`Stacks.Blowup.strictTransformIdeal_eq_ker`: the ideal cutting out the strict transform is,
with no hypothesis at all, the kernel ideal sheaf of the inclusion `j` of the complement of
`pr_{S'}⁻¹ E`. That the closed subscheme cut out by an ideal sheaf is the whole of an open
exactly when the ideal pulls back to zero there is
`AlgebraicGeometry.restrict_isIso_iff_comap_bot`, and pulling back to zero is containment in the
kernel ideal sheaf of that open's inclusion by
`AlgebraicGeometry.le_ker_iff_comap_eq_bot`; `j.ker ≤ j.ker` holds for the reason that `≤`
holds. So no quasi-coherence, retrocompactness, flatness of the centre or noetherian hypothesis
enters, and in particular neither consumer has to supply one. The same two lines serve the two
parallel strict-transform developments in the
repository, `Stacks.StrictTransform` (arbitrary `b` and `E`) and `Stacks.Blowup` (the blowup),
because both identify their defining ideal with that kernel.

For the same reason the hypothesis on the open is `V ≤ exceptionalComplement`, not equality: the
kernel ideal sheaf of an open's inclusion is antitone in the open, which is
`Stacks.IteratedBaseChange.ker_ι_le_ker_of_range_le` at the inclusion of the smaller open. That
generality is what lets the first consumer take for `V` the inverse image of an open of the
blowup, which is the shape Stacks tag 081P wants.

The local finite presentation statement needs nothing of the strict transform beyond the
identification: over the inverse image of an open of the blowup avoiding the exceptional
divisor the strict transform *is* `pr_{S'}`, which is a base change of `f`, and local finite
presentation is stable under base change and local on the target.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.StrictTransform

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)

/-- The closed subscheme of an ideal sheaf contained in the kernel of an open's inclusion
restricts to an isomorphism over every smaller open. -/
private theorem isIso_subschemeι_restrict_of_le_ker {Y : Scheme.{u}} {I : Y.IdealSheafData}
    {U V : Y.Opens} (h : I ≤ U.ι.ker) (hV : V ≤ U) : IsIso (I.subschemeι ∣_ V) :=
  (AlgebraicGeometry.restrict_isIso_iff_comap_bot _ V).mpr
    ((AlgebraicGeometry.le_ker_iff_comap_eq_bot _ _).mp
      (h.trans (Stacks.IteratedBaseChange.ker_ι_le_ker_of_range_le _ V.ι
        (by rw [Scheme.Opens.range_ι]; exact hV))))

/-- **Away from `pr_{S'}^{-1}(Supp E)` the strict transform of `X` is the plain base change
`X ×_S S'`.** The closed immersion of the strict transform restricts to an isomorphism over any
open contained in the complement of `pr_{S'}^{-1}(Supp E)`.

No hypothesis is needed: the defining ideal is unconditionally the kernel ideal sheaf of the
inclusion of that complement (`Stacks.StrictTransform.ideal_eq_ker_ι`). -/
theorem isIso_subschemeι_restrict {V : (baseChange f b).Opens}
    (hV : V ≤ exceptionalComplement f b E) :
    IsIso ((ideal f b E).subschemeι ∣_ V) :=
  isIso_subschemeι_restrict_of_le_ker (ideal_eq_ker_ι f b E).le hV

/-- Instance form of `Stacks.StrictTransform.isIso_subschemeι_restrict` at the complement of
`pr_{S'}^{-1}(Supp E)` itself. -/
instance isIso_subschemeι_restrict_exceptionalComplement :
    IsIso ((ideal f b E).subschemeι ∣_ exceptionalComplement f b E) :=
  isIso_subschemeι_restrict f b E le_rfl

end Stacks.StrictTransform

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- **Away from the inverse image of the exceptional divisor the strict transform of `X` is the
plain base change `X ×_S S'`.** The closed immersion of the strict transform restricts to an
isomorphism over any open contained in the complement of `pr_{S'}⁻¹ E`.

No hypothesis is needed: the defining ideal is unconditionally the kernel ideal sheaf of the
inclusion of that complement (`Stacks.Blowup.strictTransformIdeal_eq_ker`). -/
theorem isIso_strictTransformι_restrict {V : (blowUpPullback f ℐ).Opens}
    (hV : V ≤ exceptionalPullbackCompl f ℐ) : IsIso (strictTransformι f ℐ ∣_ V) := by
  change IsIso ((strictTransformIdeal f ℐ).subschemeι ∣_ V)
  exact Stacks.StrictTransform.isIso_subschemeι_restrict_of_le_ker
    (strictTransformIdeal_eq_ker f ℐ).le hV

/-- Instance form of `Stacks.Blowup.isIso_strictTransformι_restrict` at the complement of
`pr_{S'}⁻¹ E` itself. -/
instance isIso_strictTransformι_restrict_exceptionalPullbackCompl :
    IsIso (strictTransformι f ℐ ∣_ exceptionalPullbackCompl f ℐ) :=
  isIso_strictTransformι_restrict f ℐ le_rfl

/-- The inverse image in `X ×_S S'` of an open of the blowup disjoint from the exceptional
divisor lies in the complement of `pr_{S'}⁻¹ E`. -/
theorem preimage_le_exceptionalPullbackCompl {W : (blowUp ℐ).Opens}
    (hW : W ≤ (exceptionalIdeal ℐ).support.compl) :
    blowUpPullbackToBlowUp f ℐ ⁻¹ᵁ W ≤ exceptionalPullbackCompl f ℐ :=
  fun _ hx ↦ hW hx

/-! ### The strict transform over an open avoiding the exceptional divisor -/

/-- **The strict transform is locally of finite presentation over an open of the blowup which
avoids the exceptional divisor**, as soon as `f` is: over the inverse image of such an open the
strict transform is the projection `pr_{S'}`, which is a base change of `f`. -/
theorem locallyOfFinitePresentation_strictTransformMap_restrict
    [LocallyOfFinitePresentation f] {W : (blowUp ℐ).Opens}
    (hW : W ≤ (exceptionalIdeal ℐ).support.compl) :
    LocallyOfFinitePresentation (strictTransformMap f ℐ ∣_ W) := by
  have _ : IsIso (strictTransformι f ℐ ∣_ (blowUpPullbackToBlowUp f ℐ ⁻¹ᵁ W)) :=
    isIso_strictTransformι_restrict f ℐ (preimage_le_exceptionalPullbackCompl f ℐ hW)
  rw [strictTransformMap, morphismRestrict_comp]
  have h1 : LocallyOfFinitePresentation
      (strictTransformι f ℐ ∣_ (blowUpPullbackToBlowUp f ℐ ⁻¹ᵁ W)) := inferInstance
  have h2 : LocallyOfFinitePresentation (blowUpPullbackToBlowUp f ℐ ∣_ W) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h1 h2

/-- The strict transform is locally of finite type over the blowup as soon as `f` is locally of
finite presentation: it is a closed subscheme of a base change of `f`. -/
theorem locallyOfFiniteType_strictTransformMap [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType (strictTransformMap f ℐ) := by
  rw [strictTransformMap]
  infer_instance

open AlgebraicGeometry.FinitePresentationFromDenseOpen in
/-- **A flat strict transform is locally of finite presentation over the blowup**, provided the
exceptional divisor is avoided by some retrocompact scheme-theoretically dense open `W` of the
blowup and `f` is locally of finite presentation.

This is [Stacks, Tag 081P] (`locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`,
in the namespace `AlgebraicGeometry.FinitePresentationFromDenseOpen`)
applied to the structure morphism of the strict transform: local finiteness of type is automatic
(`Stacks.Blowup.locallyOfFiniteType_strictTransformMap`), and the local finite presentation over
`W` is `Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_restrict`, which is where
the identification of the strict transform with the base change is used. For an admissible
blowup produced by [Stacks, Tag 080Y] the exceptional divisor is exactly the complement of the
inverse image of the admissible open, and it is an effective Cartier divisor, so `W` may be taken
to be that inverse image. -/
theorem locallyOfFinitePresentation_strictTransformMap_of_flat_of_dense
    [LocallyOfFinitePresentation f] [Flat (strictTransformMap f ℐ)] (W : (blowUp ℐ).Opens)
    (hW : W ≤ (exceptionalIdeal ℐ).support.compl)
    (hretro : IsRetrocompact (W : Set (blowUp ℐ)))
    (hdense : Scheme.Opens.IsSchemeTheoreticallyDense W) :
    LocallyOfFinitePresentation (strictTransformMap f ℐ) :=
  have _ : LocallyOfFiniteType (strictTransformMap f ℐ) :=
    locallyOfFiniteType_strictTransformMap f ℐ
  have _ : LocallyOfFinitePresentation (strictTransformMap f ℐ ∣_ W) :=
    locallyOfFinitePresentation_strictTransformMap_restrict f ℐ hW
  locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open
    (strictTransformMap f ℐ) W hretro hdense

/-- The complement of the exceptional divisor of a blowup is retrocompact: the exceptional
divisor is an effective Cartier divisor ([Stacks, Tag 02OS] (2),
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData`), hence locally principal,
so its complement is affine over the blowup by [Stacks, Tag 07ZT] and in particular its
inclusion is quasi-compact. -/
theorem isRetrocompact_compl_support_exceptionalIdeal :
    IsRetrocompact (((exceptionalIdeal ℐ).support.compl : (blowUp ℐ).Opens) :
      Set (blowUp ℐ)) :=
  have _ : IsAffineHom (Scheme.Opens.ι (exceptionalIdeal ℐ).support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (isEffectiveCartierDivisor_exceptionalIdeal_reesData ℐ)
  Stacks.StrictTransform.isRetrocompact_of_quasiCompact_ι _

/-- The complement of the exceptional divisor of a blowup is scheme-theoretically dense: the
exceptional divisor is an effective Cartier divisor ([Stacks, Tag 02OS] (2)) and the complement
of such is scheme-theoretically dense ([Stacks, Tag 07ZU]). -/
theorem isSchemeTheoreticallyDense_compl_support_exceptionalIdeal :
    Scheme.Opens.IsSchemeTheoreticallyDense
      ((exceptionalIdeal ℐ).support.compl : (blowUp ℐ).Opens) :=
  Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_exceptionalIdeal_reesData ℐ)

/-- **The locally-of-finite-presentation half of [Stacks, Tag 0815] follows from its flatness
half.** If `f` is locally of finite presentation and the strict transform of `X` along the
blowup of `S` in `ℐ` is flat over the blowup, then it is locally of finite presentation over the
blowup. No further hypothesis: not quasi-compactness of `S` or `X`, not admissibility of the
centre, not noetherianness.

The dense open of [Stacks, Tag 081P] is the complement of the exceptional divisor itself, which
is retrocompact and scheme-theoretically dense because the exceptional divisor is an effective
Cartier divisor ([Stacks, Tag 02OS] (2)), and over it the strict transform is the plain
base change of `f` by `Stacks.Blowup.isIso_strictTransformι_restrict`, which is this file's
contribution. So the only input of tag 0815 that is still open is the flatness half, carried by
`AlgebraicGeometry.FinitePresentationHasFlatteningBlowup`. -/
theorem locallyOfFinitePresentation_strictTransformMap_of_flat
    [LocallyOfFinitePresentation f] [Flat (strictTransformMap f ℐ)] :
    LocallyOfFinitePresentation (strictTransformMap f ℐ) :=
  locallyOfFinitePresentation_strictTransformMap_of_flat_of_dense f ℐ
    (exceptionalIdeal ℐ).support.compl le_rfl
    (isRetrocompact_compl_support_exceptionalIdeal ℐ)
    (isSchemeTheoreticallyDense_compl_support_exceptionalIdeal ℐ)

/-! ### Lifting into the strict transform -/

/-- **A morphism to `X ×_S S'` whose restriction along a scheme-theoretically dominant morphism
lands away from the exceptional divisor factors uniquely through the strict transform.**

This is the form the valuative argument of [Stacks, Tag 02JQ] needs: for `i` the inclusion of
the generic point of the spectrum of a valuation ring — scheme-theoretically dominant because a
domain injects into its fraction field — a lift of a point of the blowup whose generic point
avoids the exceptional divisor lifts to the strict transform. Uniqueness is because the closed
immersion of the strict transform is a monomorphism. -/
theorem exists_unique_lift_strictTransformι {T T₀ : Scheme.{u}} (g : T ⟶ blowUpPullback f ℐ)
    (i : T₀ ⟶ T) [IsSchemeTheoreticallyDominant i]
    (hi : Set.range (i ≫ g) ⊆ (exceptionalPullbackCompl f ℐ : Set (blowUpPullback f ℐ))) :
    ∃! l : T ⟶ strictTransform f ℐ, l ≫ strictTransformι f ℐ = g := by
  set V := exceptionalPullbackCompl f ℐ
  have hrange : Set.range (i ≫ g) ⊆ Set.range V.ι := by
    rwa [Scheme.Opens.range_ι]
  have hle : (strictTransformι f ℐ).ker ≤ g.ker := by
    calc (strictTransformι f ℐ).ker = V.ι.ker :=
          (Scheme.IdealSheafData.ker_subschemeι _).trans (strictTransformIdeal_eq_ker f ℐ)
      _ ≤ (IsOpenImmersion.lift V.ι (i ≫ g) hrange ≫ V.ι).ker := Scheme.Hom.le_ker_comp _ _
      _ = (i ≫ g).ker := by rw [IsOpenImmersion.lift_fac]
      _ = i.ker.map g := Scheme.Hom.ker_comp i g
      _ = g.ker := by
          rw [IsSchemeTheoreticallyDominant.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  refine ⟨IsClosedImmersion.lift (strictTransformι f ℐ) g hle,
    IsClosedImmersion.lift_fac _ _ _, fun l hl ↦ ?_⟩
  rw [← cancel_mono (strictTransformι f ℐ), hl, IsClosedImmersion.lift_fac]

end Stacks.Blowup

end
