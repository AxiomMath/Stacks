module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalBaseChange
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCoherence

/-!
# The codimension-one obstruction to coherence of a direct image

Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes with complement `Z`, let `F`
be a quasi-coherent `𝒪_U`-module and let `x` be a point of `U`. [Stacks, Tag 0BK3] asserts that
`j_* F` is coherent if and only if for every `x ∈ Ass(F)`, every `z ∈ Z ∩ closure {x}` and every
associated prime `𝔭` of the completion `𝒪^∧_{closure {x}, z}` one has
`dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) ≥ 2`.

This file proves the implication (1) ⇒ (2) in contrapositive form: a one-dimensional associated
quotient of `𝒪^∧_{closure {x}, z}` for a single point `z` of `closure {x}` lying outside `U`
obstructs coherence of `j_* F`. This is the three-line last paragraph of the source's proof,
composed from the three results it cites.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.CoherentPushforwardCriterion`.

* `isCoherent_pushforward_unit_opensRange`: coherence of the direct image of the structure sheaf
  along an open immersion is coherence of the direct image along the inclusion of its open
  image.
* `not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk`: the implication (1) ⇒ (2) of
  [Stacks, Tag 0BK3], in contrapositive form at a single point.

## Implementation notes

The source's chain is run backwards from the assumed coherence of `j_* F`:

* [Stacks, Tag 0BJZ] through
  `AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_mono` carries coherence of `j_* F`
  down to coherence of `j_* i_{x,*} 𝒪_{W_x}`, where `W_x` is the reduced closure of `{x}` in
  `U`;
* [Stacks, Tag 0BK2] through
  `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_pointClosure_iff`
  rewrites that as coherence of `j'_* 𝒪_{W_x}` along the open immersion `j'` of `W_x` into the
  reduced closure of `{j x}` in `X`, whose existence is
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure`;
* the second paragraph of [Stacks, Tag 0AWC], namely
  `not_isCoherent_pushforward_structureSheaf_of_isAssociatedPrime_completedStalk` of
  `Stacks.AlgebraicGeometry.CodimensionOneObstruction`, contradicts that: the reduced closure of
  `{j x}` is integral and locally Noetherian, and `z` is a point of it outside the image of
  `j'`.

The last step is stated in the tree for the inclusion `V.ι` of an open subscheme rather than for
an abstract open immersion, so `isCoherent_pushforward_unit_opensRange` converts between the
two; it is the composite of `AlgebraicGeometry.Scheme.Hom.isoOpensRange` with the two existing
identifications `AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrict` and
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` of the direct image of a structure sheaf
along an isomorphism.

Two features of the statement are inherited rather than chosen.

The monomorphism `φ : i_{x,*} 𝒪_{W_x} ⟶ F` stands in for the hypothesis `x ∈ Ass(F)` of the
source, which is used there only to produce such a map. Its construction is the part of
[Stacks, Tag 0BJZ] that the tree does not carry out, so the only available form of that lemma —
`AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_mono` — takes the map as a hypothesis,
and this statement inherits it.

The hypothesis on `𝔭` is `dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) = 1` rather than the `≤ 1` that negating
clause (2) of the source literally gives. The remaining case `dim = 0` says that the maximal
ideal of `𝒪^∧_{closure {x}, z}` is associated, which cannot happen — the closure of `{x}` is
integral and `z` is not its generic point, so its local ring at `z` is a domain of positive
dimension and therefore has positive depth, as does its completion. That argument is not in the
tree, and the second paragraph of [Stacks, Tag 0AWC] is itself stated with `= 1`.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

open CodimensionOneObstruction

/-- **Coherence of a direct image of a structure sheaf is read on the open image.** For an open
immersion `f : A ⟶ B`, coherence of `f_* 𝒪_A` gives coherence of the direct image of the
structure sheaf of the open subscheme `f.opensRange` of `B` along its inclusion.

The source `A` is isomorphic to `f.opensRange` over `B`, and the direct image of a structure
sheaf along an isomorphism of schemes is a structure sheaf. -/
theorem isCoherent_pushforward_unit_opensRange {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f]
    (hf : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit A.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward f.opensRange.ι).obj
      (SheafOfModules.unit f.opensRange.toScheme.ringCatSheaf)).IsCoherent := by
  have := hf
  set e := f.isoOpensRange with he
  have : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  have eu : (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit A.ringCatSheaf) ≅
      SheafOfModules.unit f.opensRange.toScheme.ringCatSheaf :=
    Scheme.Modules.pushforwardIsoRestrict e _ ≪≫ Scheme.Modules.restrictUnitIso e.inv
  exact CoherentDevissage.isCoherent_of_iso
    ((Scheme.Modules.pushforward f.opensRange.ι).mapIso eu.symm ≪≫
      (Scheme.Modules.pushforwardComp e.hom f.opensRange.ι).app _ ≪≫
      (Scheme.Modules.pushforwardCongr (Scheme.Hom.isoOpensRange_hom_ι f)).app _)

/-- **[Stacks, Tag 0BK3], the implication (1) ⇒ (2), in contrapositive form at a single point.**
Let `j : U ⟶ X` be an open immersion of schemes with `X` locally Noetherian, let `F` be a
quasi-coherent `𝒪_U`-module and let `x` be a point of `U`. Write `W_x` for the reduced closure
of `{x}` in `U` and `closure {x}` for the reduced closure of `{j x}` in `X`. Suppose there is a
monomorphism `i_{x,*} 𝒪_{W_x} ⟶ F`, and suppose `z` is a point of `closure {x}` whose image in
`X` lies outside `U` such that the completion `𝒪^∧_{closure {x}, z}` has an associated prime `𝔭`
with `dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) = 1`. Then `j_* F` is not coherent.

This is the failure of clause (2) of the source at `x` and `z` obstructing clause (1). The
monomorphism replaces the source's `x ∈ Ass(F)`, which enters the argument only through the map
it produces; and the associated quotient is assumed one-dimensional rather than at most
one-dimensional. See the module documentation for why neither restriction is avoidable here. -/
@[stacks 0BK3 "(1) implies (2), contrapositive at one point, for a one-dimensional associated \
quotient of the completion and given a monomorphism from the structure sheaf of the point closure",
  ega "IV 5.11.4" "necessity"]
theorem not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    {F : U.Modules} [F.IsQuasicoherent]
    (φ : pointClosureStructureSheaf x ⟶ F) [Mono φ]
    {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set X)))
    (z : I.subscheme) (hz : I.subschemeι z ∉ j.opensRange)
    {p : PrimeSpectrum (I.subscheme.completedLocalRingCat z)}
    (hp : IsAssociatedPrimeStacks (I.subscheme.completedLocalRingCat z)
      (I.subscheme.completedLocalRingCat z) p.asIdeal)
    (hdim : ringKrullDim (I.subscheme.completedLocalRingCat z ⧸ p.asIdeal) = 1) :
    ¬ ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  subst hI
  intro hF
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  -- The closure of `{x}` in `X` is integral and locally Noetherian.
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure _
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure _
  -- Step 1, [Stacks, Tag 0BJZ]: coherence descends along the monomorphism.
  have h1 : ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent :=
    isCoherent_pushforward_pointClosure_of_mono j x φ hF
  -- The commutative square of point closures.
  obtain ⟨j', hj', comm⟩ := Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure j x
  have := hj'
  -- Step 2, [Stacks, Tag 0BK2]: coherence transfers to the closure of `{j x}`.
  have h2 := (ClosedImmersionCoherence.isCoherent_pushforward_pointClosure_iff j x j' comm).mp h1
  -- Step 3: read it on the open image of `j'`.
  have h3 := isCoherent_pushforward_unit_opensRange j' h2
  -- `z` lies outside that open image, since its image in `X` lies outside `U`.
  have hzV : z ∉ j'.opensRange := by
    rintro ⟨w, hw⟩
    refine hz ?_
    have hcomm : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι (j' w) =
        j ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι w) := by
      simpa using congrArg (fun g : _ ⟶ X => g.base w) comm
    rw [← hw, hcomm]
    exact ⟨_, rfl⟩
  -- The open image is nonempty because the closure of `{x}` in `U` is.
  have : Nonempty j'.opensRange.toScheme :=
    ⟨⟨j' (genericPoint (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme), ⟨_, rfl⟩⟩⟩
  -- Step 4, the second paragraph of [Stacks, Tag 0AWC].
  exact not_isCoherent_pushforward_structureSheaf_of_isAssociatedPrime_completedStalk
    hzV hp hdim h3

end Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

end
