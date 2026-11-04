module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.IntegralModel
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral

/-!
# The class at infinity and the restrictions of a class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre
at infinity `i_∞ : W_∞ ⟶ W`, section at zero `i_0 : X ⟶ W` and class `C ∈ A⁰(W_∞ ⟶ X)` of
Stacks 0F9J. On a test scheme `T ⟶ X`, `C ∩ α = i_∞^* β` for every `β ∈ A_{k+1}(W ×_X T)` lifting
`α`, that is, restricting on the chart `b^{-1}(𝐀¹_X) ×_X T` to the flat pullback of `α`.

The chart is an affine line over `T`, so flat pullback to it is surjective (Stacks 02TT) and every
class on `W ×_X T` is a lift. The divisor `D_0` of the chart maps isomorphically to `T`, and its
Gysin map inverts flat pullback (Stacks 02TR). From these, for every class `q ∈ A^p(W)`, a lift
`β` of `α` gives a lift `q ∩ β` of `i_0^* q ∩ α`; together with the Gysin naturality of `q` at the
divisor at infinity this gives

  `C ∘ i_0^* q = q|_{W_∞} ∘ C`   in   `A^p(W_∞ ⟶ X)`,

the general form of the second equality of Stacks 0FAV. With the generic form of Stacks 0F9K,
`(Z ⟶ X)_* ∘ q' = i_0^* q`, it gives Stacks 0FAV for every localized class, and in particular for
`c'_p(Q)` and `P'_p(Q)`. Lastly, `β` lifts the pushforward of `i_∞^* β` to `T`, which is
Stacks 0FAR: `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`.

## Main definitions

* `Stacks.Chow.modificationZeroRestriction` — the restriction `i_0^* q ∈ A^p(X)`.
* `Stacks.Chow.modificationInfinityRestriction` — the restriction `q|_{W_∞} ∈ A^p(W_∞)`.

## Main results

* `Stacks.Chow.isAffineSpaceBundle_modificationAffineChartProjection`,
  `Stacks.Chow.flatPullbackChow_modificationAffineChartProjection_surjective` — the chart over
  `𝐀¹_X` is an affine line over `T`, and flat pullback to it is surjective (Stacks 02TT).
* `Stacks.Chow.exists_isModificationLift_of_class` — every class on `W ×_X T` is a lift.
* `Stacks.Chow.IsModificationLift.idRule` — if `β` lifts `α`, then `q ∩ β` lifts `i_0^* q ∩ α`.
* `Stacks.Chow.idRule_modificationInfinityGysin` — `q|_{W_∞} ∩ i_∞^* β = i_∞^*(q ∩ β)`.
* `Stacks.Chow.gysinAtInfinityClass_comp_modificationZeroRestriction` —
  `C ∘ i_0^* q = q|_{W_∞} ∘ C`.
* `Stacks.Chow.gysinAtInfinityClass_comp_localizedModificationClass` — the generic form of
  Stacks 0FAV: `C ∘ (Z ⟶ X)_* ∘ q' = q|_{W_∞} ∘ C`.
* `Stacks.Chow.gysinAtInfinityClass_comp_modificationChernClass` — **Stacks 0FAV**:
  `C ∘ c_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{W_∞}) ∘ C`; and
  `Stacks.Chow.gysinAtInfinityClass_comp_modificationPowerSum`, the same for `P'_p(Q)`.
* `Stacks.Chow.gysinCapOfLift_chowPush_modificationInfinityGysin` — **Stacks 0FAR**, on every
  test scheme.

## Implementation notes

The class `C` is `Stacks.Chow.gysinAtInfinityClass`, whose cap operation is
`Stacks.Chow.gysinCapAtInfinity`; the proofs use its construction from lifts, not only the identity
`i_{∞,*} ∘ C = i_{0,*}`, which does not determine it.

The composites `C ∘ i_0^* q` and `q|_{W_∞} ∘ C` of Stacks 0B75 are classes for `W_∞ ⟶ X ⟶ X` of
degree `0 + p` and for `W_∞ ⟶ W_∞ ⟶ X` of degree `p + 0`; both are read as classes for
`W_∞ ⟶ X` of degree `p` by `Stacks.Chow.BivariantClass.copy`. The restriction `i_0^* q` is a
class against the structure morphism `X ⟶ W ⟶ S`, read against that of `X` by
`Stacks.Chow.bivariantClassCongrBase`, as on the right side of
`Stacks.Chow.properPushforwardChowCohomology_localizedModificationClass`.

The source states Stacks 0FAR as an identity of bivariant classes; it is stated here on every test
scheme `T ⟶ X`, of which the case `T = X` is the statement for `X` itself. In Stacks 0FAV,
`c_p(Q|_{W_∞})` is the Chern class of the derived pullback of `Q` to `W_∞`, which is the
restriction of `c_p(Q)` (`Stacks.Chow.res_perfectChernClass_derivedPullback_of_comp_eq`).

## References

* [Stacks Project, Tag 0FAV](https://stacks.math.columbia.edu/tag/0FAV)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The chart over `𝐀¹_X` is an affine line over the test scheme -/

/-- The projection `𝐀¹_X ⟶ X` is an affine-space bundle of rank one: it is isomorphic over `X`
to the projection of Mathlib's affine space `𝔸¹_X`. -/
theorem isAffineSpaceBundle_affineLineOver_fst (X : Scheme.{u}) :
    IsAffineSpaceBundle
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) 1 :=
  FreeTower.isAffineSpaceBundle_of_iso (affineLineOverIsoAffineSpace X ≪≫
    (AffineSpace.functor.mapIso (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u + 1}).toIso.op).app X)
    ((Category.assoc _ _ _).trans
      ((congrArg (toAffineSpace X ≫ ·) (AffineSpace.reindex_over _ X)).trans
        (toAffineSpace_fst X)))

/-- **The chart over `𝐀¹_X` is an affine-space bundle of rank one over the test scheme.** When
`b : W ⟶ 𝐏¹_X` is an isomorphism over `𝐀¹_X`, the projection `b^{-1}(𝐀¹_X) ×_X T ⟶ T` is the
base change of `𝐀¹_X ⟶ X` along `T ⟶ X`. -/
theorem isAffineSpaceBundle_modificationAffineChartProjection {X S W T : Scheme.{u}}
    (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsAffineSpaceBundle (modificationAffineChartProjection f b g) 1 :=
  isAffineSpaceBundle_of_isPullback (isPullback_modificationAffineChartProjection f b g hA)
    (isAffineSpaceBundle_affineLineOver_fst X)

/-! ### Restriction of the operation of a class to an open subscheme of a test scheme -/

section IdentityRuleRestrict

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Z : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {p : ℤ}

/-- The operation of a class `a ∈ A^p(Z)` on a test scheme commutes with restriction to an open
subscheme `v : T' ⟶ T` of the test scheme, the structure morphism of `T'` being presented by an
equality `v ≫ g = m`. This is Stacks 0B76 (2) in relative dimension zero. -/
theorem BivariantClass.idRule_chowGroupRestrict (a : chowCohomologyComponent C G sZ p)
    {T T' : Scheme.{u}} (g : T ⟶ Z) [LocallyOfFiniteType g] (v : T' ⟶ T) [IsOpenImmersion v]
    (m : T' ⟶ Z) [LocallyOfFiniteType m] (hm : v ≫ g = m) (k : ℤ)
    (x : chowGroup C (g ≫ sZ) k) :
    chowGroupRestrict C (g ≫ sZ) (m ≫ sZ) v (by rw [← hm, Category.assoc]) (k - p)
        (a.idRule C sZ G g k x) =
      a.idRule C sZ G m k
        (chowGroupRestrict C (g ≫ sZ) (m ≫ sZ) v (by rw [← hm, Category.assoc]) k x) := by
  have hr := relativeDimension_of_isOpenImmersion v
  have h1 := heq_chowGroupRestrict_flatPullbackChow C (g ≫ sZ) (m ≫ sZ) v
    (by rw [← hm, Category.assoc]) hr (k - p) (flatPullbackDescends C _ _ _ _ _ _ _)
    (a.idRule C sZ G g k x)
  have h2 := a.idRule_flatPullbackChow C G sZ g v 0 hr m hm k x
  have h3 := heq_chowGroupRestrict_flatPullbackChow C (g ≫ sZ) (m ≫ sZ) v
    (by rw [← hm, Category.assoc]) hr k (flatPullbackDescends C _ _ _ _ _ _ _) x
  exact eq_of_heq (h1.trans (h2.symm.trans (IdentityCapRule.heq_congr C sZ (a.idRule C sZ G) rfl
    (by simp) h3.symm)))

end IdentityRuleRestrict

/-! ### Stacks 02TT and 02TR on the chart over `𝐀¹_X` -/

section AffineChart

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (g : T ⟶ X) [LocallyOfFiniteType g]

/-- **Stacks 02TT for the chart over `𝐀¹_X`.** Flat pullback along the projection
`b^{-1}(𝐀¹_X) ×_X T ⟶ T` is surjective on Chow groups in every degree. -/
theorem flatPullbackChow_modificationAffineChartProjection_surjective (k : ℤ) :
    haveI := flat_modificationAffineChartProjection f b g hA
    Function.Surjective (flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
      (modificationAffineChartProjection f b g) (modificationAffineChartProjection_over C f b g)
      1 (relativeDimension_modificationAffineChartProjection f b g hA) k
      (flatPullbackDescends C _ _ _ _ _ _ k)) :=
  have := flat_modificationAffineChartProjection f b g hA
  flatPullbackChow_surjective_of_isAffineSpaceBundle_general C _ _ _ _ 1 _
    (isAffineSpaceBundle_modificationAffineChartProjection f b g hA) k

/-- **Every class on `W ×_X T` is a lift.** Every `β ∈ A_{k+1}(W ×_X T)` lifts some
`α ∈ A_k(T)`: its restriction to the chart over `𝐀¹_X` is a flat pullback from `T`
(Stacks 02TT). -/
theorem exists_isModificationLift_of_class (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    ∃ α, IsModificationLift C f b hA g k α β := by
  obtain ⟨α, hα⟩ := flatPullbackChow_modificationAffineChartProjection_surjective C f b hA g k
    (chowGroupRestrict C (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g)
      (modificationAffineChartι f b g) rfl (k + 1) β)
  exact ⟨α, hα.symm⟩

/-- **Stacks 02TR on the chart over `𝐀¹_X`, in every degree.** The Gysin map of the pulled-back
divisor `D_0` of the chart is a left inverse of flat pullback along the projection to `T`, read on
`D_0` through the isomorphism `D_0 ≅ T`. -/
theorem gysinSystemOfInvertible_onChow_flatPullbackChow_modificationAffineChart (n : ℤ)
    (α : chowGroup C (g ≫ f) n) :
    haveI := flat_modificationAffineChartProjection f b g hA
    haveI := isIso_modificationAffineZeroScheme_comp f b g hA
    (gysinSystemOfInvertible C).onChow (modificationAffineChartOver C f b g)
        ((Scheme.Modules.pullback (modificationAffineChartι f b g)).obj
          (lineZeroModule (modificationBaseChangeToRelativeLine f b g)))
        (AlgebraicGeometry.pullbackGlobalSections (modificationAffineChartι f b g) _
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))) n
        (flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
          (modificationAffineChartProjection f b g)
          (modificationAffineChartProjection_over C f b g) 1
          (relativeDimension_modificationAffineChartProjection f b g hA) n
          (flatPullbackDescends C _ _ _ _ _ _ n) α) =
      chowPushforwardOfIso C (g ≫ f)
        ((modificationAffineZeroScheme f b g).subschemeι ≫ modificationAffineChartOver C f b g)
        (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
          modificationAffineChartProjection f b g))
        (by rw [IsIso.inv_comp_eq, Category.assoc, modificationAffineChartProjection_over]) n
        α := by
  have := flat_modificationAffineChartProjection f b g hA
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  exact gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso C _ (g ≫ f) _
    (modificationAffineChartProjection_over C f b g)
    (relativeDimension_modificationAffineChartProjection f b g hA) _ _
    (isRelativeEffectiveCartierDivisor_modificationAffineZeroScheme f b g hA) m α

end AffineChart

/-- Transport along an equality of degrees, as `Eq.mp` of the congruence on Chow groups. -/
private theorem chowGroupDegreeEquiv_eq_mp (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {a b : ℤ} (h : a = b) (x : chowGroup C sY a) :
    chowGroupDegreeEquiv C sY h x = Eq.mp (congrArg (chowGroup C sY) h) x :=
  eq_of_heq ((chowGroupDegreeEquiv_heq C sY h x).trans (eq_mp_chowGroup_heq C sY h x).symm)

/-! ### The restriction of a class to the section at zero, and lifts -/

section ZeroRestriction

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) {p : ℤ}

/-- **The restriction `i_0^* q`.** For a class `q ∈ A^p(W)`, its restriction along the section at
zero `i_0 : X ⟶ W` (Stacks 0B7F), read against the structure morphism of `X` through
`X ⟶ W ⟶ X = 𝟙 X`. -/
abbrev modificationZeroRestriction
    (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      p) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) f p :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
    (by rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp])
    (by rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp])
    (hv := Category.id_comp _) (hv' := Category.id_comp f) p
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f)
      (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q)

variable (g : T ⟶ X) [LocallyOfFiniteType g]
  (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)

/-- **The operation of `q` on a flat pullback to the chart over `𝐀¹_X`.** For `α ∈ A_k(T)`, the
class `q ∩ pr^* α` on the chart `b^{-1}(𝐀¹_X) ×_X T` is the flat pullback of `i_0^* q ∩ α`. By
Stacks 02TT it is the flat pullback of some `γ`; the Gysin map of the divisor `D_0` of the chart,
which maps isomorphically to `T`, recovers `γ` from `pr^* γ` (Stacks 02TR) and commutes with `q`,
so `γ = i_0^*(q ∩ pr^* α) = q ∩ i_0^* pr^* α = i_0^* q ∩ α`. -/
theorem idRule_flatPullbackChow_modificationAffineChart (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    haveI := flat_modificationAffineChartProjection f b g hA
    chowGroupDegreeEquiv C (modificationAffineChartOver C f b g) (by ring : k + 1 - p = k - p + 1)
        (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
          (modificationAffineChartι f b g ≫ pullback.fst (modificationProjection f b) g) (k + 1)
          (flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
            (modificationAffineChartProjection f b g)
            (modificationAffineChartProjection_over C f b g) 1
            (relativeDimension_modificationAffineChartProjection f b g hA) k
            (flatPullbackDescends C _ _ _ _ _ _ k) α)) =
      flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
        (modificationAffineChartProjection f b g) (modificationAffineChartProjection_over C f b g)
        1 (relativeDimension_modificationAffineChartProjection f b g hA) (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ (k - p))
        ((modificationZeroRestriction C f b hA q).idRule C f (gysinSystemOfInvertible C) g k
          α) := by
  have := flat_modificationAffineChartProjection f b g hA
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  obtain ⟨γ, hγ⟩ := flatPullbackChow_modificationAffineChartProjection_surjective C f b hA g
    (k - p) (chowGroupDegreeEquiv C (modificationAffineChartOver C f b g)
      (by ring : k + 1 - p = k - p + 1)
      (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
        (modificationAffineChartι f b g ≫ pullback.fst (modificationProjection f b) g) (k + 1)
        (flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
          (modificationAffineChartProjection f b g)
          (modificationAffineChartProjection_over C f b g) 1
          (relativeDimension_modificationAffineChartProjection f b g hA) k
          (flatPullbackDescends C _ _ _ _ _ _ k) α)))
  refine hγ.symm.trans (congrArg _ ?_)
  have hm : inv ((modificationAffineZeroScheme f b g).subschemeι ≫
      modificationAffineChartProjection f b g) ≫
      ((modificationAffineZeroScheme f b g).subschemeι ≫
        modificationAffineChartι f b g ≫ pullback.fst (modificationProjection f b) g) =
      g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) := by
    have h1 := modificationSectionAtZeroBaseChange_eq f b g hA
    simp only [← Category.assoc] at h1 ⊢
    rw [← h1]
    exact pullback.lift_fst _ _ _
  have hs : (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) ≫
      modificationProjection f b ≫ f = g ≫ f := by
    rw [Category.assoc, ← Category.assoc (modificationSectionAtZero _ _ _),
      modificationSectionAtZero_comp_projection f b hA, Category.id_comp]
  refine chowPushforwardOfIso_injective C (g ≫ f)
    ((modificationAffineZeroScheme f b g).subschemeι ≫ modificationAffineChartOver C f b g)
    (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
      modificationAffineChartProjection f b g))
    (by rw [IsIso.inv_comp_eq, Category.assoc, modificationAffineChartProjection_over]) (k - p) ?_
  rw [← gysinSystemOfInvertible_onChow_flatPullbackChow_modificationAffineChart C f b hA g (k - p)
    γ, hγ]
  have hgys := q.idRule_gysin C (modificationProjection f b ≫ f)
    (modificationAffineChartι f b g ≫ pullback.fst (modificationProjection f b) g)
    ((Scheme.Modules.pullback (modificationAffineChartι f b g)).obj
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g)))
    (AlgebraicGeometry.pullbackGlobalSections (modificationAffineChartι f b g) _
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))) k
    (flatPullbackChow C (modificationAffineChartOver C f b g) (g ≫ f)
      (modificationAffineChartProjection f b g)
      (modificationAffineChartProjection_over C f b g) 1
      (relativeDimension_modificationAffineChartProjection f b g hA) k
      (flatPullbackDescends C _ _ _ _ _ _ k) α)
  have hi0 : (modificationZeroRestriction C f b hA q).idRule C f (gysinSystemOfInvertible C) g k
      α = chowGroupCongr C hs (k - p)
        (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
          (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) k
          (chowGroupCongr C hs.symm k α)) := by
    rw [BivariantClass.idRule_bivariantClassCongrBase, chowCohomologyRestriction_idRule,
      chowGroupCongr_chowGroupCongr]
    rfl
  refine (congrArg _ (chowGroupDegreeEquiv_eq_mp C _ _ _)).trans (hgys.symm.trans ?_)
  refine (congrArg _ (gysinSystemOfInvertible_onChow_flatPullbackChow_modificationAffineChart C f b
    hA g k α)).trans ?_
  refine (BivariantClass.idRule_chowPush_of_eq q _ _ _ hm (g ≫ f) hs _ k α).trans ?_
  exact (congrArg _ hi0).symm

/-- **Lifts are natural under a class of `A^p(W)`.** If `β ∈ A_{k+1}(W ×_X T)` lifts
`α ∈ A_k(T)`, then `q ∩ β` lifts `i_0^* q ∩ α`: restricted to the chart over `𝐀¹_X`, the class
`q ∩ β` is `q ∩ pr^* α` (Stacks 0B76 (2) for the open immersion of the chart), which is
`pr^*(i_0^* q ∩ α)` by `Stacks.Chow.idRule_flatPullbackChow_modificationAffineChart`. The degree
`(k + 1) - p` of `q ∩ β` is read as `(k - p) + 1`. -/
theorem IsModificationLift.idRule {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)}
    (hβ : IsModificationLift C f b hA g k α β) :
    IsModificationLift C f b hA g (k - p)
      ((modificationZeroRestriction C f b hA q).idRule C f (gysinSystemOfInvertible C) g k α)
      (chowGroupDegreeEquiv C (modificationBaseChangeOver f b g) (by ring : k + 1 - p = k - p + 1)
        (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjection f b) g) (k + 1) β)) := by
  have := flat_modificationAffineChartProjection f b g hA
  unfold IsModificationLift at hβ ⊢
  have h1 := BivariantClass.idRule_chowGroupRestrict q (pullback.fst (modificationProjection f b) g)
    (modificationAffineChartι f b g) _ rfl (k + 1) β
  refine Eq.trans ?_ (idRule_flatPullbackChow_modificationAffineChart C f b hA g q k α)
  refine (chowGroupRestrict_chowGroupDegreeEquiv C _ _ _ _ _ _).trans ?_
  exact congrArg _ (h1.trans (congrArg _ hβ))

/-- **Gysin naturality of a class at the divisor at infinity.** The restriction `q|_{W_∞}` of a
class `q ∈ A^p(W)`, operating on `W_∞ ×_X T`, commutes with the Gysin map at infinity:
`q|_{W_∞} ∩ i_∞^* β = i_∞^*(q ∩ β)`. This is Stacks 0B76 (3) for `q` at the pulled-back divisor
at infinity, whose zero scheme is identified with `W_∞ ×_X T`, together with Stacks 0B76 (1)
for that identification. The degree `(k + 1) - p` of `q ∩ β` is read as `(k - p) + 1`. -/
theorem idRule_modificationInfinityGysin (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q).idRule C
        (modificationProjectionAtInfinity f b ≫ f) (gysinSystemOfInvertible C)
        (pullback.fst (modificationProjectionAtInfinity f b) g) k
        (modificationInfinityGysin C f b g k β) =
      modificationInfinityGysin C f b g (k - p)
        (chowGroupDegreeEquiv C (modificationBaseChangeOver f b g)
          (by ring : k + 1 - p = k - p + 1)
          (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
            (pullback.fst (modificationProjection f b) g) (k + 1) β)) := by
  have hm : (modificationInfinityZeroSchemeIso f b g).hom ≫
      pullback.fst (modificationProjectionAtInfinity f b) g ≫
        modificationInclusionAtInfinity f b =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
        pullback.fst (modificationProjection f b) g := by
    rw [← modificationInfinityBaseChange_comp_fst, ← Category.assoc,
      modificationInfinityZeroSchemeIso_hom_comp]
  refine (chowCohomologyRestriction_idRule C _ (modificationInclusionAtInfinity f b) q
    (pullback.fst (modificationProjectionAtInfinity f b) g) k _).trans ?_
  refine (q.idRule_chowPush C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) g ≫ modificationInclusionAtInfinity f b)
    (modificationInfinityZeroSchemeIso f b g).hom _ hm k
    ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
      (modificationInfinityModule f b g) (modificationInfinitySection f b g) k β)).trans ?_
  exact congrArg _ ((q.idRule_gysin C (modificationProjection f b ≫ f)
    (pullback.fst (modificationProjection f b) g) (modificationInfinityModule f b g)
    (modificationInfinitySection f b g) k β).trans
    (congrArg _ (chowGroupDegreeEquiv_eq_mp C _ _ _).symm))

end ZeroRestriction

/-! ### The class at infinity and the restrictions of a class -/

section GysinAtInfinityComposite

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) {p : ℤ}
  (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)

/-- **The restriction `q|_{W_∞}`.** For a class `q ∈ A^p(W)`, its restriction along the inclusion
`i_∞ : W_∞ ⟶ W` of the fibre at infinity (Stacks 0B7F), a class of `A^p(W_∞)`. -/
abbrev modificationInfinityRestriction :
    chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f) p :=
  Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
    (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q

/-- **The class at infinity intertwines the two restrictions of a class** (the general form of the
second equality of Stacks 0FAV). For every class `q ∈ A^p(W)`,

  `C ∘ i_0^* q = q|_{W_∞} ∘ C`   in   `A^p(W_∞ ⟶ X)`,

where `C ∈ A⁰(W_∞ ⟶ X)` is the class of Stacks 0F9J, `i_0^* q ∈ A^p(X)` and
`q|_{W_∞} ∈ A^p(W_∞)` are the restrictions of `q` to the section at zero and to the fibre at
infinity, and `∘` is the composition of Stacks 0B75. On a test scheme, with `β` a lift of `α`:
`C ∩ (i_0^* q ∩ α) = i_∞^*(q ∩ β)` because `q ∩ β` lifts `i_0^* q ∩ α`, and
`i_∞^*(q ∩ β) = q|_{W_∞} ∩ i_∞^* β = q|_{W_∞} ∩ (C ∩ α)` by Gysin naturality of `q`. The two
composites, classes for `W_∞ ⟶ X ⟶ X` and `W_∞ ⟶ W_∞ ⟶ X` of degrees `0 + p` and `p + 0`, are
both read as classes for `W_∞ ⟶ X` of degree `p`. -/
theorem gysinAtInfinityClass_comp_modificationZeroRestriction :
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add p)
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA) (modificationZeroRestriction C f b hA q)) =
      BivariantClass.copy C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) f
        (Category.id_comp (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq (Category.id_comp _) rfl) rfl (add_zero p)
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _)
          (modificationProjectionAtInfinity f b) (Category.id_comp _) rfl p 0
          (modificationInfinityRestriction C f b q) (gysinAtInfinityClass C f b hA)) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k α ↦ ?_
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g k α
  refine eq_of_heq ((BivariantClass.copy_cap C _ _ _ _ _ _ _ _ g k α).trans
    (HEq.trans ?_ (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ g k α).symm))
  refine (supportedRightComp_cap C _ _ _ _ (gysinAtInfinityClass C f b hA)
    (modificationZeroRestriction C f b hA q) g k α).trans (HEq.trans ?_
      (supportedLeftComp_cap C _ _ _ _ (modificationInfinityRestriction C f b q)
        (gysinAtInfinityClass C f b hA) g k α).symm)
  have h1 : (gysinAtInfinityClass C f b hA).cap g (k - p)
      ((modificationZeroRestriction C f b hA q).idRule C f (gysinSystemOfInvertible C) g k α) ≍
      modificationInfinityGysin C f b g (k - p)
        (chowGroupDegreeEquiv C (modificationBaseChangeOver f b g)
          (by ring : k + 1 - p = k - p + 1)
          (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
            (pullback.fst (modificationProjection f b) g) (k + 1) β)) := by
    rw [gysinAtInfinityClass_cap]
    exact (chowGroupDegreeEquiv_heq C _ _ _).trans (heq_of_eq
      (gysinCapAtInfinity_eq_of_isModificationLift C f b hA g (k - p) _ _
        (hβ.idRule C f b hA g q)))
  have h2 : (modificationInfinityRestriction C f b q).idRule C
      (modificationProjectionAtInfinity f b ≫ f) (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) g) k
      (modificationInfinityGysin C f b g k β) ≍
      (modificationInfinityRestriction C f b q).idRule C
      (modificationProjectionAtInfinity f b ≫ f) (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
      ((gysinAtInfinityClass C f b hA).cap g k α) := by
    refine IdentityCapRule.heq_congr C _ _ rfl (sub_zero k).symm ?_
    rw [gysinAtInfinityClass_cap, gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k α β
      hβ]
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm
  exact h1.trans ((heq_of_eq (idRule_modificationInfinityGysin C f b g q k β).symm).trans h2)

/-- The intertwining `C ∘ i_0^* q = q|_{W_∞} ∘ C` of
`Stacks.Chow.gysinAtInfinityClass_comp_modificationZeroRestriction`, stated for the two
composites themselves, classes for the two spellings `W_∞ ⟶ X ⟶ X` and
`W_∞ ⟶ W_∞ ⟶ X` of `W_∞ ⟶ X` and of the two degrees `0 + p` and `p + 0`. -/
theorem gysinAtInfinityClass_comp_modificationZeroRestriction_heq :
    bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
        (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
        (gysinAtInfinityClass C f b hA) (modificationZeroRestriction C f b hA q) ≍
      bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _)
        (modificationProjectionAtInfinity f b) (Category.id_comp _) rfl p 0
        (modificationInfinityRestriction C f b q) (gysinAtInfinityClass C f b hA) := by
  have hcopy : ∀ {F F' : modificationFibreAtInfinity f b ⟶ X} [LocallyOfFiniteType F]
      [LocallyOfFiniteType F'] (e : F = F') (hF : F ≫ f = modificationProjectionAtInfinity f b ≫ f)
      (hF' : F' ≫ f = modificationProjectionAtInfinity f b ≫ f) {n n' : ℤ} (hn : n = n')
      (c : BivariantClass C (gysinSystemOfInvertible C) _ f F hF n),
      BivariantClass.copy C _ _ f e hF hF' hn c ≍ c := by
    intro F F' _ _ e hF hF' n n' hn c
    subst e hn
    rfl
  exact (hcopy _ _ _ _ _).symm.trans ((heq_of_eq
    (gysinAtInfinityClass_comp_modificationZeroRestriction C f b hA q)).trans (hcopy _ _ _ _ _))

end GysinAtInfinityComposite

/-! ### Stacks 0FAV -/

section LocalizedClass

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t]

/-- **The generic form of Stacks 0FAV.** Let `T ⊆ W_∞` be closed and contain every point of `W_∞`
over `X ∖ Z`, and let `q ∈ A^p(W)` vanish over `T`, with localized class `q' ∈ A^p(Z ⟶ X)`
(`Stacks.Chow.localizedModificationClass`, at the class of Stacks 0F9J). Then

  `C ∘ (Z ⟶ X)_* ∘ q' = q|_{W_∞} ∘ C`   in   `A^p(W_∞ ⟶ X)`:

by the generic form of Stacks 0F9K, `(Z ⟶ X)_* ∘ q' = i_0^* q`, and `C ∘ i_0^* q = q|_{W_∞} ∘ C`
(`Stacks.Chow.gysinAtInfinityClass_comp_modificationZeroRestriction`).
-/
theorem gysinAtInfinityClass_comp_localizedModificationClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t) {p : ℤ}
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add p)
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (properPushforwardChowCohomology C f (z ≫ f) z rfl
            (localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq))) =
      BivariantClass.copy C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) f
        (Category.id_comp (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq (Category.id_comp _) rfl) rfl (add_zero p)
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _)
          (modificationProjectionAtInfinity f b) (Category.id_comp _) rfl p 0
          (modificationInfinityRestriction C f b q) (gysinAtInfinityClass C f b hA)) := by
  rw [properPushforwardChowCohomology_localizedModificationClass]
  exact gysinAtInfinityClass_comp_modificationZeroRestriction C f b
    hA q

attribute [local instance 10000] HasDerivedCategory.standard

variable {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

/-- In the situation of Stacks 0F9K, let `Q|_T` be finite locally free of rank `< p` in degree
`0`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J (`Stacks.Chow.gysinAtInfinityClass`).
Then

  `C ∘ c_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{W_∞}) ∘ C`   in   `A^p(W_∞ ⟶ X)`,

where `c'_p(Q)` is `Stacks.Chow.modificationChernClass`, `Q|_{X × {0}}` and `Q|_{W_∞}` are the
derived pullbacks of `Q` along the section at zero and the inclusion of the fibre at infinity,
and `∘` is the composition of Stacks 0B75. The composites, of degrees `0 + p` and `p + 0` for
`W_∞ ⟶ X ⟶ X` and `W_∞ ⟶ W_∞ ⟶ X`, are read as classes of degree `p` for `W_∞ ⟶ X`. -/
@[stacks 0FAV "C ∘ c_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{W_∞}) ∘ C, for Q|_T \
finite locally free of rank < p in degree 0, the composites read in A^p(W_∞ ⟶ X)"]
theorem gysinAtInfinityClass_comp_modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (perfectChernClass C f (hQ.derivedPullback
            (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) p)) =
      BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f)
        f (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (properPushforwardChowCohomology C f (z ≫ f) z rfl
            (modificationChernClass C f b hA z t hQ p hT hrank))) ∧
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (properPushforwardChowCohomology C f (z ≫ f) z rfl
            (modificationChernClass C f b hA z t hQ p hT hrank))) =
      BivariantClass.copy C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) f
        (Category.id_comp (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq (Category.id_comp _) rfl) rfl (add_zero (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _)
          (modificationProjectionAtInfinity f b) (Category.id_comp _) rfl p 0
          (perfectChernClass C (modificationProjectionAtInfinity f b ≫ f)
            (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p)
          (gysinAtInfinityClass C f b hA)) := by
  refine ⟨by rw [properPushforwardChowCohomology_modificationChernClass], ?_⟩
  have hres : perfectChernClass C (modificationProjectionAtInfinity f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p =
      modificationInfinityRestriction C f b
        (perfectChernClass C (modificationProjection f b ≫ f) hQ p) :=
    (congrArg (fun c : TotalChowClass C _ ↦ c p)
      (res_perfectChernClass_derivedPullback_of_comp_eq C
      (modificationProjection f b ≫ f) hQ (sX' := modificationProjectionAtInfinity f b ≫ f)
      (modificationInclusionAtInfinity f b) rfl (hQ.derivedPullback _))).symm.trans
      (TotalChowClass.res_apply_eq_bivariantClassCongrBase (modificationInclusionAtInfinity f b) rfl
        _ p)
  rw [hres]
  exact gysinAtInfinityClass_comp_localizedModificationClass C f b
    hA z t hT (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank)

/-- **Stacks 0FAV for `P'_p`.** In the situation of Stacks 0F9K, let `Q|_T` be zero. Then

  `C ∘ P_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{W_∞}) ∘ C`   in   `A^p(W_∞ ⟶ X)`,

where `P'_p(Q)` is `Stacks.Chow.modificationPowerSum` and `C` is the class of Stacks 0F9J, the
composites being read as in
`Stacks.Chow.gysinAtInfinityClass_comp_modificationChernClass`. -/
theorem gysinAtInfinityClass_comp_modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (perfectPowerSumComponent C f (hQ.derivedPullback
            (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) p)) =
      BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f)
        f (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (properPushforwardChowCohomology C f (z ≫ f) z rfl
            (modificationPowerSum C f b hA z t hQ p hT hzero))) ∧
    BivariantClass.copy C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
        (Category.comp_id (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) rfl (zero_add (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
          (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 p
          (gysinAtInfinityClass C f b hA)
          (properPushforwardChowCohomology C f (z ≫ f) z rfl
            (modificationPowerSum C f b hA z t hQ p hT hzero))) =
      BivariantClass.copy C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) f
        (Category.id_comp (modificationProjectionAtInfinity f b))
        (comp_comp_structureMorphism_eq (Category.id_comp _) rfl) rfl (add_zero (p : ℤ))
        (bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _)
          (modificationProjectionAtInfinity f b) (Category.id_comp _) rfl p 0
          (perfectPowerSumComponent C (modificationProjectionAtInfinity f b ≫ f)
            (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p)
          (gysinAtInfinityClass C f b hA)) := by
  refine ⟨by rw [properPushforwardChowCohomology_modificationPowerSum], ?_⟩
  have hres : perfectPowerSumComponent C (modificationProjectionAtInfinity f b ≫ f)
      (hQ.derivedPullback (modificationInclusionAtInfinity f b)) p =
      modificationInfinityRestriction C f b
        (perfectPowerSumComponent C (modificationProjection f b ≫ f) hQ p) :=
    (congrArg (fun c : TotalChowClass C _ ↦ c p) (res_perfectPowerSum_derivedPullback C
      (modificationProjection f b ≫ f) hQ (sX' := modificationProjectionAtInfinity f b ≫ f)
      (modificationInclusionAtInfinity f b) rfl (hQ.derivedPullback _) p)).symm.trans
      (TotalChowClass.res_apply_eq_bivariantClassCongrBase (modificationInclusionAtInfinity f b) rfl
        _ p)
  rw [hres]
  exact gysinAtInfinityClass_comp_localizedModificationClass C f b
    hA z t hT (vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hzero)

end LocalizedClass

/-! ### Stacks 0FAR -/

section PushforwardGysin

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (g : T ⟶ X) [LocallyOfFiniteType g]

/-- In the situation of Stacks 0F9J, `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`, on every test scheme
`g : T ⟶ X`: for `β ∈ A_{k+1}(W ×_X T)`, the cap operation of the class `C` of Stacks 0F9J on the
pushforward of `i_∞^* β` along `W_∞ ×_X T ⟶ T` is `i_∞^* β`. The identity of bivariant classes is
the case `g = 𝟙 X`. -/
@[stacks 0FAR "C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*, on every test scheme T ⟶ X"]
theorem gysinCapOfLift_chowPush_modificationInfinityGysin (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    gysinCapAtInfinity C f b hA g k
        (chowPush C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
          (pullback.snd (modificationProjectionAtInfinity f b) g)
          (modificationInfinityBaseChange_snd_over f b g) k
          (modificationInfinityGysin C f b g k β)) =
      modificationInfinityGysin C f b g k β := by
  have := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
  obtain ⟨γ, hγ⟩ := exists_isModificationLift_of_class C f b hA g k β
  have hcap := gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k γ β hγ
  have hpush : chowPush C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjectionAtInfinity f b) g)
      (modificationInfinityBaseChange_snd_over f b g) k (modificationInfinityGysin C f b g k β) =
      γ := by
    rw [← hcap]
    refine (chowPush_comp C _ _ _ (modificationInfinityBaseChange f b g)
      (pullback.snd (modificationProjection f b) g) _
      (modificationInfinityBaseChange_comp_snd f b g) (modificationInfinityBaseChange_over f b g)
      (modificationBaseChange_snd_over f b g) _ k _).symm.trans ?_
    refine (congrArg (chowPush C (modificationBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjection f b) g) (modificationBaseChange_snd_over f b g) k)
      (chowPushforward_gysinCapOfLift C f b g hA k γ)).trans ?_
    refine (chowPush_comp C _ _ _ _ (pullback.snd (modificationProjection f b) g) (𝟙 T)
      (modificationSectionAtZeroBaseChange_comp_snd f b g _ _) _
      (modificationBaseChange_snd_over f b g) (Category.id_comp _) k γ).trans ?_
    exact chowPush_id C _ k γ
  rw [hpush, hcap]

end PushforwardGysin

end Stacks.Chow

end
