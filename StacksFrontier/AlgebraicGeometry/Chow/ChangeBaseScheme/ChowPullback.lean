module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FamilyDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferenceCarrier
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Chow groups under a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c`, that is a flat
morphism `g : S' ⟶ S` of the two bases whose dimension functions differ by `c` on the generic
points of the fibres of `g`, and let `f : X ⟶ S` be locally of finite type, with base change
`X' = X ×_S S'`. The homomorphism `Stacks.Chow.baseChangeCyclePullback` of cycle groups
`Z_k(X) ⟶ Z_{k+c}(X')` carries cycles rationally equivalent to zero to cycles rationally
equivalent to zero, and therefore induces a homomorphism `CH_k(X) ⟶ CH_{k+c}(X')` of Chow
groups. That is Stacks 0FVJ, and it is what this file proves.

## Main definitions

* `Stacks.Chow.baseChangeChowPullback` — the induced homomorphism
  `CH_k(X) ⟶ CH_{k+c}(X')` on Chow groups.

## Main results

* `Stacks.Chow.baseChangeCyclePullback_maps_rationalEquivalences` — **Stacks 0FVJ**, flat base
  change of cycles preserves rational equivalence to zero.
* `Stacks.Chow.baseChangeChowPullback_mk` — the induced homomorphism sends the class of a cycle
  to the class of the base change of that cycle.
* `Stacks.Chow.baseChangeCyclePullbackOfIsPullback_fibreDifference` — base change along an
  arbitrary cartesian square takes the fibre difference of a family member to the fibre
  difference of its base change.

## Implementation notes

By Stacks 02S4 part (4) a cycle rationally equivalent to zero is the total fibre difference of a
locally finite family `W` of integral closed subschemes of `X ×_S 𝐏¹_S`, each of relative
dimension `k + 1` at its generic points and contained in neither distinguished section. Base
changing the family member by member gives a locally finite family in `X' ×_{S'} 𝐏¹_{S'}`, and
the base change of the cycle is the total fibre difference of that family: base change of cycles
multiplies the coefficient at the image point in `X` by a weight depending only on the point of
`X'`, so it commutes with the locally finite sum, and it carries the two fibre cycles of a member
to the two fibre cycles of its base change by Stacks 0FVI part (1).

A base-changed member need no longer be integral, so Stacks 02S4 part (2) is unavailable for it;
Stacks 02S5 is what applies, in the carrier-refined form
`Stacks.Chow.fibreDifference_isRationallyEquivalentToZeroWithin`, so that the individual
equivalences may be summed over the family by `Stacks.Chow.rationallyEquivalentToZero_finsum`.
Its three dimension hypotheses are proved in
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FamilyDimension`. Its hypothesis on
associated points is proved here: the projection from a base-changed member to the member is a
base change of `g`, hence flat, so an associated point of the base change lies over the generic
point of the integral member, and that generic point misses both sections because the member is
contained in neither and the sections have closed image.

## References

* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Associated points of a scheme flat over an integral scheme -/

/-- **An associated point of a scheme flat over an integral scheme lies over the generic
point.** For `q : Y ⟶ X` flat with `X` integral and `Y` locally Noetherian, every associated
point of `Y` is carried by `q` to the generic point of `X`.

Read on an affine chart `V ⊆ q⁻¹U`, the point is an associated prime 𝔮 of `Γ(Y, V)`, so some
element `b` of `Γ(Y, V)` has annihilator exactly 𝔮. Flatness of `Γ(X, U) ⟶ Γ(Y, V)` makes `b`
torsion-free over `Γ(X, U)`, so the contraction of 𝔮 — the prime of `Γ(X, U)` corresponding to
the image point — is the zero ideal, which on the integral scheme `X` is the generic point. -/
private theorem map_eq_genericPoint_of_mem_schemeAssociatedPoints {Y X : Scheme.{u}} (q : Y ⟶ X)
    [Flat q] [IsIntegral X] [IsLocallyNoetherian Y] (y : Y)
    (hy : y ∈ Stacks.Divisors.schemeAssociatedPoints Y) :
    q y = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (q ⁻¹ᵁ U).isOpen
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  have : Nonempty U := ⟨⟨q y, hx⟩⟩
  let φ := (q.appLE U V hVU).hom
  let _ : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, V) := q.flat_appLE hU hV hVU
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  have hp :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      (SheafOfModules.unit Y.ringCatSheaf) V hV hyV).mpr hy
  change IsAssociatedPrimeStacks Γ(Y, V) Γ(Y, V) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal at hp
  obtain ⟨hprime, b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    intro hh
    apply hprime.one_notMem
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    simp [hh]
  have hpbot : (hU.primeIdealOf ⟨q y, hx⟩).asIdeal = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    show a = 0
    have ha' : φ a ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
      have hnat := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hyV
      rw [← hnat] at ha
      exact ha
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot] at ha'
    change φ a * b = 0 at ha'
    have hz : a • (b : Γ(Y, V)) = 0 := ha'
    exact (smul_eq_zero.mp hz).resolve_right hb0
  have hη : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr (by simpa using ‹Nonempty U›)
  have heq : hU.primeIdealOf ⟨q y, hx⟩ = hU.primeIdealOf ⟨genericPoint X, hη⟩ := by
    apply PrimeSpectrum.ext
    rw [hpbot, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  simpa only [hU.fromSpec_primeIdealOf] using congrArg hU.fromSpec heq

/-! ### The cycle of an inverse-image closed subscheme -/

/-- If an ideal sheaf `J` on `X'` is the inverse image of an ideal sheaf `I` on `X` along
`q : X' ⟶ X`, then its cycle is the cycle of the second projection of the fibre product of the
closed subscheme of `I` with `q`: the two closed immersions differ by the canonical isomorphism
presenting the inverse image as that fibre product, composed with the symmetry of the fibre
product. -/
private theorem cycleAssociatedToClosedSubscheme_eq_snd_of_eq_comap (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (q : X' ⟶ X)
    {I : X.IdealSheafData} {J : X'.IdealSheafData} (h : J = I.comap q) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sX' J.subschemeι k =
      cycleAssociatedToClosedSubscheme C sX' (pullback.snd I.subschemeι q) k := by
  subst h
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C sX' (I.comap q).subschemeι
    (pullback.snd I.subschemeι q) (I.comapIso q ≪≫ pullbackSymmetry q I.subschemeι)
    (by
      rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
        Scheme.IdealSheafData.comapIso_hom_fst]) k

/-! ### The fibre difference of a base-changed family -/

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (f : X ⟶ B.base.S)
  [LocallyOfFiniteType f]

/-- **Base change takes the fibre difference of a family member to the fibre difference of its
base change.** Both fibres of the base-changed member are the inverse images of the fibres of
the member, and the base change of the cycle of a closed subscheme of delta-dimension at most
`k` is the cycle of its base change by Stacks 0FVI part (1). -/
private theorem baseChangeCyclePullback_fibreDifference (k : ℤ)
    (W : (projectiveLineProduct f).IdealSheafData)
    (h₀ : schemeDeltaDimension B.base ((zeroFiber f W).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension B.base ((infinityFiber f W).subschemeι ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullback B f k (fibreDifference B.base f k W) =
      fibreDifference B.baseChange (pullback.snd f B.g) (k + B.c)
        (baseChangedFamily f B.g W) := by
  simp only [fibreDifference]
  rw [map_sub,
    baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B f (zeroFiber f W).subschemeι k h₀,
    baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B f
      (infinityFiber f W).subschemeι k hInf,
    cycleAssociatedToClosedSubscheme_eq_snd_of_eq_comap B.baseChange (pullback.snd f B.g) _
      (zeroFiber_baseChangedFamily f B.g W) (k + B.c),
    cycleAssociatedToClosedSubscheme_eq_snd_of_eq_comap B.baseChange (pullback.snd f B.g) _
      (infinityFiber_baseChangedFamily f B.g W) (k + B.c)]

/-- **Base change along an arbitrary cartesian square takes the fibre difference of a family
member to the fibre difference of its base change.** This is
`Stacks.Chow.baseChangeCyclePullback_fibreDifference` for a cartesian square `p ≫ f = q ≫ g`
realizing the base change, in place of the chosen fibre product `X ×_S S'`.

Both fibres of the pulled-back member are the inverse images along `p` of the fibres of the
member, and the base change of the cycle of a closed subscheme of delta-dimension at most `k` is
the cycle of its base change by Stacks 0FVI part (1) along the square. -/
theorem baseChangeCyclePullbackOfIsPullback_fibreDifference (hc : B.c = 0) {Y : Scheme.{u}}
    {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
    (k : ℤ) (W : (projectiveLineProduct f).IdealSheafData)
    (h₀ : schemeDeltaDimension B.base ((zeroFiber f W).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension B.base ((infinityFiber f W).subschemeι ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullbackOfIsPullback B hc f sq k (fibreDifference B.base f k W) =
      fibreDifference B.baseChange q k (baseChangedFamilyOfSquare f B.g sq.w W) := by
  simp only [fibreDifference]
  rw [map_sub,
    baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme B hc f sq
      (zeroFiber f W).subschemeι k h₀,
    baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme B hc f sq
      (infinityFiber f W).subschemeι k hInf,
    cycleAssociatedToClosedSubscheme_eq_snd_of_eq_comap B.baseChange q _
      (zeroFiber_baseChangedFamilyOfSquare f B.g sq.w W) k,
    cycleAssociatedToClosedSubscheme_eq_snd_of_eq_comap B.baseChange q _
      (infinityFiber_baseChangedFamilyOfSquare f B.g sq.w W) k]

/-! ### Associated points of a base-changed family -/

/-- The projection from the base change of a closed subscheme of `X ×_S 𝐏¹_S` to that closed
subscheme. -/
private def baseChangedFamilyProjection {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) :
    (baseChangedFamily f g W).subscheme ⟶ W.subscheme :=
  show (W.comap (projectiveLineProductBaseChange f g)).subscheme ⟶ W.subscheme from
    (W.comapIso (projectiveLineProductBaseChange f g)).hom ≫
      pullback.snd (projectiveLineProductBaseChange f g) W.subschemeι

/-- The projection of a base-changed family lies over the base-change morphism of the two
families of projective lines. -/
private theorem baseChangedFamilyProjection_comp {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) :
    baseChangedFamilyProjection f g W ≫ W.subschemeι =
      (baseChangedFamily f g W).subschemeι ≫ projectiveLineProductBaseChange f g := by
  show ((W.comapIso (projectiveLineProductBaseChange f g)).hom ≫
      pullback.snd (projectiveLineProductBaseChange f g) W.subschemeι) ≫ W.subschemeι =
    (W.comap (projectiveLineProductBaseChange f g)).subschemeι ≫
      projectiveLineProductBaseChange f g
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- **An associated point of a base-changed family misses the constant sections.** If an
integral closed subscheme `W ⊆ X ×_S 𝐏¹_S` is not contained in the image of the constant
section at a closed point `e` of `𝐏¹_ℤ`, then no associated point of the base change of `W`
lies on the constant section at `e` of the base-changed family.

The projection from the base change of `W` to `W` is a base change of the flat morphism `g`,
hence flat, so an associated point of the base change lies over the generic point of `W`. That
generic point does not lie on the section: the inverse image of the section in `W` is closed,
and a closed set containing the generic point is everything, which `W` being contained in no
section forbids. -/
private theorem notMem_range_constantSection_of_mem_schemeAssociatedPoints
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) [IsClosedImmersion e]
    (hW : ¬ Set.range W.subschemeι ⊆ Set.range (constantSection f e))
    (ζ : (baseChangedFamily f B.g W).subscheme)
    (hζ : ζ ∈ Stacks.Divisors.schemeAssociatedPoints (baseChangedFamily f B.g W).subscheme) :
    (baseChangedFamily f B.g W).subschemeι ζ ∉
      Set.range (constantSection (pullback.snd f B.g) e) := by
  have : Flat (baseChangedFamilyProjection f B.g W) :=
    MorphismProperty.of_isPullback (isPullback_familyBase_baseChangedFamily B f W).flip B.flat
  have : IsLocallyNoetherian (baseChangedFamily f B.g W).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W))
  have : IsClosedImmersion (constantSection f e) := isClosedImmersion_constantSection f e
  have hgen : baseChangedFamilyProjection f B.g W ζ = genericPoint W.subscheme :=
    map_eq_genericPoint_of_mem_schemeAssociatedPoints (baseChangedFamilyProjection f B.g W) ζ hζ
  have hη : W.subschemeι (genericPoint W.subscheme) ∉ Set.range (constantSection f e) := by
    have hclosed : IsClosed (W.subschemeι ⁻¹' Set.range (constantSection f e)) :=
      (constantSection f e).isClosedEmbedding.isClosed_range.preimage W.subschemeι.continuous
    intro hmem
    have hall := ((genericPoint_spec W.subscheme).mem_closed_set_iff hclosed).mp hmem
    exact hW (by rintro _ ⟨z, rfl⟩; exact hall (Set.mem_univ z))
  rintro ⟨z, hz⟩
  refine hη ?_
  have hsq : W.subschemeι (baseChangedFamilyProjection f B.g W ζ) =
      projectiveLineProductBaseChange f B.g ((baseChangedFamily f B.g W).subschemeι ζ) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun a ↦ a ζ) (baseChangedFamilyProjection_comp f B.g W)
  rw [← hgen, hsq, ← hz]
  exact ⟨pullback.fst f B.g z, by
    simpa only [Scheme.Hom.comp_apply] using
      (congrArg (fun a ↦ a z)
        (constantSection_comp_projectiveLineProductBaseChange f B.g e)).symm⟩

/-! ### Stacks 0FVJ -/

/-- **Stacks Project, Tag 0FVJ, preservation of rational equivalence.** In a flat base-change
situation with dimension shift `c`, the base-change homomorphism on cycle groups carries
`k`-cycles rationally equivalent to zero on `X` to `(k + c)`-cycles rationally equivalent to
zero on `X' = X ×_S S'`.

By Stacks 02S4 part (4) such a cycle is the total fibre difference of a locally finite family of
integral closed subschemes of `X ×_S 𝐏¹_S`, each of relative dimension `k + 1` at its generic
points and contained in neither distinguished section. Its base change is the total fibre
difference of the base-changed family, which is again locally finite, and each member of the
base-changed family satisfies the hypotheses of Stacks 02S5 over the new base: the dimension
bounds are those of
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FamilyDimension`, and the condition on
associated points holds because the projection to the original member is flat. The individual
equivalences are summed by `Stacks.Chow.rationallyEquivalentToZero_finsum`, the carriers of the
members forming a locally finite family. -/
@[stacks 0FVJ "preservation of rational equivalence"]
theorem baseChangeCyclePullback_maps_rationalEquivalences (k : ℤ) :
    rationalEquivalences B.base f k ≤
      (rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c)).comap
        (baseChangeCyclePullback B f k) := by
  intro α hα
  obtain ⟨J, W, hInt, hDim, h₀, hInf, hLoc, hcoeff⟩ :=
    exists_familyFibreDifferences B.base f k α hα
  have hzero : ∀ j, schemeDeltaDimension B.base ((zeroFiber f (W j)).subschemeι ≫ f) ≤
      (k : EInt) := by
    intro j
    have := hInt j
    exact schemeDeltaDimension_zeroFiber_le B.base f (W j) (hDim j) (h₀ j)
  have hinfty : ∀ j, schemeDeltaDimension B.base ((infinityFiber f (W j)).subschemeι ≫ f) ≤
      (k : EInt) := by
    intro j
    have := hInt j
    exact schemeDeltaDimension_infinityFiber_le B.base f (W j) (hDim j) (hInf j)
  refine rationallyEquivalentToZero_finsum B.baseChange (pullback.snd f B.g) (k + B.c)
    (fun j ↦ fibreDifference B.baseChange (pullback.snd f B.g) (k + B.c)
      (baseChangedFamily f B.g (W j)))
    (fun j ↦ fibreCarrier B.baseChange (pullback.snd f B.g) (baseChangedFamily f B.g (W j)))
    (locallyFinite_fibreCarrier B.baseChange (pullback.snd f B.g) _
      (locallyFinite_support_baseChangedFamily f B.g W hLoc)) (fun j ↦ ?_) fun x ↦ ?_
  · have := hInt j
    refine fibreDifference_isRationallyEquivalentToZeroWithin B.baseChange (pullback.snd f B.g)
      (k + B.c) (baseChangedFamily f B.g (W j))
      (relativeDimension_familyBase_baseChangedFamily_le B f (W j) (hDim j))
      (schemeDeltaDimension_zeroFiber_baseChangedFamily_le B f (W j) (hDim j) (h₀ j))
      (schemeDeltaDimension_infinityFiber_baseChangedFamily_le B f (W j) (hDim j) (hInf j))
      fun ζ hζ ↦ Or.inl ⟨?_, ?_⟩
    · exact notMem_range_constantSection_of_mem_schemeAssociatedPoints B f (W j)
        integralZeroSection (h₀ j) ζ hζ
    · exact notMem_range_constantSection_of_mem_schemeAssociatedPoints B f (W j)
        integralInfinitySection (hInf j) ζ hζ
  · calc (baseChangeCyclePullback B f k α).1 x
        = α.1 ((pullback.fst f B.g).base x) *
            flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g)
              (k + B.c) x := baseChangeCyclePullback_apply B f k α x
      _ = (∑ᶠ j : J, (fibreDifference B.base f k (W j)).1 ((pullback.fst f B.g).base x)) *
            flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g)
              (k + B.c) x := by rw [hcoeff]; rfl
      _ = ∑ᶠ j : J, (fibreDifference B.base f k (W j)).1 ((pullback.fst f B.g).base x) *
            flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g)
              (k + B.c) x := finsum_mul _ _
      _ = ∑ᶠ j : J,
            (baseChangeCyclePullback B f k (fibreDifference B.base f k (W j))).1 x := rfl
      _ = ∑ᶠ j : J, (fibreDifference B.baseChange (pullback.snd f B.g) (k + B.c)
            (baseChangedFamily f B.g (W j))).1 x :=
          finsum_congr fun j ↦ congrArg
            (fun z : CycleGroup B.baseChange (pullback.snd f B.g) (k + B.c) ↦ z.1 x)
            (baseChangeCyclePullback_fibreDifference B f k (W j) (hzero j) (hinfty j))

/-- **Stacks Project, Tag 0FVJ, the map on Chow groups.** The homomorphism
`g^* : CH_k(X) ⟶ CH_{k+c}(X ×_S S')` induced on Chow groups by the base-change homomorphism
on cycle groups, which preserves rational equivalence by
`Stacks.Chow.baseChangeCyclePullback_maps_rationalEquivalences`. -/
@[stacks 0FVJ "induced map on Chow groups"]
def baseChangeChowPullback (k : ℤ) :
    chowGroup B.base f k →+ chowGroup B.baseChange (pullback.snd f B.g) (k + B.c) :=
  QuotientAddGroup.map (rationalEquivalences B.base f k)
    (rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c))
    (baseChangeCyclePullback B f k) (baseChangeCyclePullback_maps_rationalEquivalences B f k)

/-- The base-change homomorphism on Chow groups sends the class of a cycle to the class of the
base change of that cycle. -/
theorem baseChangeChowPullback_mk (k : ℤ) (a : CycleGroup B.base f k) :
    baseChangeChowPullback B f k (QuotientAddGroup.mk' (rationalEquivalences B.base f k) a) =
      QuotientAddGroup.mk' (rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c))
        (baseChangeCyclePullback B f k a) :=
  rfl

end Stacks.Chow

end
