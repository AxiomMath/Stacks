module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.LargerOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionDepth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionUniqueness

/-!
# The restriction isomorphism over a larger open subscheme

Let `X` be locally Noetherian, let `U ⟶ U' ⟶ X` be a chain of open immersions whose total
range has a complement of depth at least two in `X`, let `π : V ⟶ U` be a finite étale cover
and let `Y = Spec_X(𝓑)` be the canonical extension of that cover across the complement, for
`𝓑 = (π ≫ i ≫ k)_* 𝒪_V`. Suppose a finite étale cover `π' : V' ⟶ U'` of the larger open
subscheme restricts over `U` to `π`. Then the restriction of `Y` to `U'` is isomorphic to `π'`
over `U'`, by exactly one isomorphism compatible with the two prescribed identifications over
`U`.

## Main results

* `Stacks.FundamentalGroup.ExtendedEtaleFold.existsUnique_restrictionIso` — the `larger_open`
  clause of [Stacks, Tag 0EY6].

## Implementation notes

Both `Y ×_X U'` and `V'` are finite over `U'`, both restrict over `U` to the cover `π`, and
both have local rings of depth at least two above the complement of `U` in `U'`: for `Y ×_X U'`
this is `two_le_depth_pullback` applied to the depth clause `extendedEtale_depth_ge_two`, and
for `V'` it is the depth condition on `U'` itself, carried across the étale stalk maps of `π'`.
So the uniqueness clause `extendedEtale_unique`, applied over the base `U'` with its restricted
depth hypothesis `two_le_depth_restrict`, identifies each of them with the extension of `π`
across the complement of `U` in `U'`, and composing those two identifications gives the
isomorphism. Uniqueness is uniqueness in that clause, transported by the slice-category
bookkeeping of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.LargerOpen`:
`coverMapOfPullbackIso` turns an identification of restrictions into a morphism out of `V`, and
`pullback_map_comp_eq_of_coverMap_comp` together with
`coverMap_comp_eq_of_pullback_map_comp` says that a morphism of slice objects respects the
identifications exactly when it respects those morphisms.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-- **The `larger_open` clause of [Stacks, Tag 0EY6].** Let `i : U ⟶ U'` and `k : U' ⟶ X` be
open immersions into a locally Noetherian scheme with `X ∖ (i ≫ k)(U)` of depth at least two,
let `π : V ⟶ U` be a finite étale cover and let `Y = Spec_X(𝓑)` be its canonical extension, for
`𝓑 = (π ≫ i ≫ k)_* 𝒪_V`. Given a finite étale cover `π' : V' ⟶ U'` of the larger open
subscheme, an identification `eY` of the restriction of `Y` to `U` with `π`, and an
identification `eV` of the restriction of `π'` to `U` with `π`, there is exactly one
isomorphism over `U'` between the restriction of `Y` to `U'` and `π'` whose own restriction to
`U` carries `eV` back to `eY`.

Both `Y ×_X U'` and `V'` are finite over `U'`, restrict over `U` to `π`, and have depth at
least two above `U' ∖ i(U)`; so `extendedEtale_unique`, over the base `U'`, identifies each
with the extension of `π` across that complement, and the isomorphism is the composite of those
two identifications. Its uniqueness is the uniqueness in that clause. -/
@[stacks 0EY6 "larger_open"]
public theorem existsUnique_restrictionIso {U U' X V V' : Scheme.{u}} [IsLocallyNoetherian X]
    (i : U ⟶ U') [IsOpenImmersion i] (k : U' ⟶ X) [IsOpenImmersion k]
    (π : V ⟶ U) [IsFinite π] [Etale π] (π' : V' ⟶ U') [IsFinite π'] [Etale π']
    (hdepth : ∀ x : X, x ∉ ((i ≫ k).opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    let Y := gluedSpectrum (extendedEtaleSituation (i ≫ k) π hdepth)
    ∀ (eY : (Over.pullback (i ≫ k)).obj (Over.mk Y.toBase) ≅ Over.mk π)
      (eV : (Over.pullback i).obj (Over.mk π') ≅ Over.mk π),
      ∃! e : (Over.pullback k).obj (Over.mk Y.toBase) ≅ Over.mk π',
        (Over.pullbackComp i k).hom.app (Over.mk Y.toBase) ≫
          (Over.pullback i).map e.hom ≫ eV.hom = eY.hom := by
  intro Y
  have : IsLocallyNoetherian U' := isLocallyNoetherian_of_isOpenImmersion k
  have hdepthU := two_le_depth_restrict i k hdepth
  have : IsLocallyNoetherian (extendedEtaleSituation (i ≫ k) π hdepth).base :=
    inferInstanceAs (IsLocallyNoetherian X)
  have : IsFinite Y.toBase := isFinite_relativeSpectrum_extendedEtaleSituation (i ≫ k) π hdepth
  have : IsLocallyNoetherian Y.scheme := LocallyOfFiniteType.isLocallyNoetherian Y.toBase
  -- the restriction of the canonical extension to the larger open subscheme
  let P : Over U' := (Over.pullback k).obj (Over.mk Y.toBase)
  let fP : P.left ⟶ U' := P.hom
  have : IsFinite fP := by
    change IsFinite (pullback.snd Y.toBase k)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback Y.toBase k) inferInstance
  -- the canonical extension of the cover across the complement of `U` in `U'`
  let R := gluedSpectrum (extendedEtaleSituation i π hdepthU)
  have hdepthV : ∀ v : V', π' v ∉ (i.opensRange : Set U') →
      (2 : ℕ∞) ≤ Module.depth (V'.presheaf.stalk v)
        (IsLocalRing.maximalIdeal (V'.presheaf.stalk v)) (V'.presheaf.stalk v) := by
    intro v hv
    let : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian π'
    rw [(RingHom.depth_eq_of_isEtaleLocalHom (π'.stalkMap v).hom
      ((AlgebraicGeometry.etale_iff_forall_isEtaleAt π').mp inferInstance v)).symm]
    exact hdepthU (π' v) hv
  intro eY eV
  -- the identification of the restriction of `P` to `U` with the cover
  let eRest : (Over.pullback i).obj P ≅ Over.mk π :=
    ((Over.pullbackComp i k).app (Over.mk Y.toBase)).symm ≪≫ eY
  let c : V ⟶ P.left := coverMapOfPullbackIso i P π eRest
  have hc : IsPullback π c i fP := by
    simpa only [P, fP] using isPullback_coverMapOfPullbackIso i P π eRest
  obtain ⟨a, ha, haUnique⟩ := extendedEtale_unique i π hdepthU fP c hc
    (two_le_depth_pullback i k Y.toBase (extendedEtale_depth_ge_two (i ≫ k) π hdepth))
  let aOver : P ≅ Over.mk R.toBase := Over.isoMk a ha.1
  let cV : V ⟶ V' := coverMapOfPullbackIso i (Over.mk π') π eV
  have hcV : IsPullback π cV i π' := by
    simpa only [Over.mk_hom] using isPullback_coverMapOfPullbackIso i (Over.mk π') π eV
  obtain ⟨b, hb, -⟩ := extendedEtale_unique i π hdepthU π' cV hcV hdepthV
  let bOver : Over.mk π' ≅ Over.mk R.toBase := Over.isoMk b hb.1
  let e := aOver ≪≫ bOver.symm
  have hcan : c ≫ e.hom.left = cV := by
    change c ≫ a.hom ≫ b.inv = cV
    rw [← Category.assoc, Iso.comp_inv_eq, ha.2, hb.2]
  have hrest := pullback_map_comp_eq_of_coverMap_comp i P π (Over.mk π') eRest eV e hcan
  have hcompRest : (Over.pullbackComp i k).hom.app (Over.mk Y.toBase) ≫ eRest.hom = eY.hom := by
    simp [eRest]
  refine ⟨e, by beta_reduce; rw [hrest, hcompRest], fun e' he' => ?_⟩
  have hcan' : c ≫ e'.hom.left = cV :=
    coverMap_comp_eq_of_pullback_map_comp i P π (Over.mk π') eRest eV e'
      ((cancel_epi ((Over.pullbackComp i k).hom.app (Over.mk Y.toBase))).mp
        (he'.trans hcompRest.symm))
  let candidate : P.left ≅ R.scheme := (Over.forget U').mapIso e' ≪≫ b
  have hcand : candidate.hom = e'.hom.left ≫ b.hom := rfl
  have hcover : candidate.hom ≫ R.toBase = fP ∧
      c ≫ candidate.hom = extendedEtaleCoverMap i π hdepthU :=
    ⟨by rw [hcand, Category.assoc, hb.1]; exact Over.w e'.hom,
      by rw [hcand, ← Category.assoc, hcan', hb.2]⟩
  have hleft : e'.hom.left = a.hom ≫ b.inv := by
    rw [Iso.eq_comp_inv]
    simpa only [hcand] using congrArg Iso.hom (haUnique candidate hcover)
  exact Iso.ext (CostructuredArrow.hom_ext e'.hom e.hom hleft)

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
