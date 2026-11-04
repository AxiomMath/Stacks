module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseTensor
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChangeGeneral

/-!
# Localized Chern classes are compatible with base change

Let `(S, δ)`, `X`, `i : Z ⟶ X`, `E ∈ D(𝒪_X)` and `p ≥ 0` be as in Situation 0GUJ
(`Stacks.Chow.LocalizedSituation`), and let `f : X' ⟶ X` be locally of finite type, with
`E' = Lf^*E` and `Z' = f^{-1}(Z) = Z ×_X X'`. The data `X'`, `Z'`, `E'`, `p` again form a
situation as in 0GUJ (`Stacks.Chow.LocalizedSituation.pullback`). **Stacks 0FB3** says that
the localized classes of Stacks 0FB2 for it are the restrictions (Remark 0F9Z) of those for `X`:

  `P_p(Z' ⟶ X', E') = res P_p(Z ⟶ X, E)`,   resp.   `c_p(Z' ⟶ X', E') = res c_p(Z ⟶ X, E)`.

The proof is the source's. Let `b : W ⟶ 𝐏¹_X`, `Q` and `b' : W' ⟶ 𝐏¹_{X'}`, `Q'` be the graph
constructions for `E` and `E'`. The composite `W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X` is good for the triple of
`E`, so by Stacks 0GTY and 0F8V it factors through `b` by some `k : W' ⟶ W` with `Q' ≅ Lk^*Q`.
The localized class of Stacks 0F9K for `b'`, `Q'` is then the restriction of the one for `b`, `Q`
(`Stacks.Chow.bivariantRestriction_localizedModificationClass_of_lift`, which combines Stacks 0GUI
with the second assertion of Stacks 0FAU), for any choice of the closed subschemes of the fibres
at infinity (the first assertion of Stacks 0FAU).

## Main definitions

* `Stacks.Chow.LocalizedChernData.pullback` — the base change of the data `X`, `Z`, `E`, `p`
  of conditions (1) and (2) of Situation 0GUJ along `f : X' ⟶ X`.
* `Stacks.Chow.LocalizedSituation.pullback` — the base change of Situation 0GUJ along
  `f : X' ⟶ X`.

## Main results

* `Stacks.Chow.LocalizedChernData.restriction_pullback`,
  `Stacks.Chow.LocalizedSituation.finiteness_pullback` — conditions (2) and (3) of
  Situation 0GUJ are stable under base change.
* `Stacks.Chow.exists_lift_graphBlowupToBase_and_iso` — the morphism `k : W' ⟶ W` of graph
  constructions over `𝐏¹_{X'} ⟶ 𝐏¹_X`, with `Lk^*Q ≅ Q'`.
* `Stacks.Chow.bivariantRestriction_modificationPowerSum_of_lift`,
  `Stacks.Chow.bivariantRestriction_modificationChernClass_of_lift` — the restriction of
  `P'_p(Q)`, resp. `c'_p(Q)`, along a morphism of modifications `k` with `Q' ≅ Lk^*Q`.
* `Stacks.Chow.LocalizedSituation.bivariantRestriction_localizedPowerSum`,
  `Stacks.Chow.LocalizedSituation.bivariantRestriction_localizedChern` — **Stacks 0FB3**.

## Implementation notes

The restriction of Remark 0F9Z is `Stacks.Chow.bivariantRestriction`, a class for the chosen
fibre product `Z ×_X X' ⟶ X'` whose source lies over the base through `Z`; the localized class of
the base-changed situation has the same source `Z' = Z ×_X X'`, lying over the base through `X'`.
These are equal morphisms and not the same term, and `Stacks.Chow.bivariantClassCongrBase` reads
the first class against the second.

Condition (3) of Situation 0GUJ is carried along `f` as follows: the alternatives (a) and (b) for
`X` give the alternative (d) for `X'` through `f`, the alternative (c) is preserved because the
termwise pullback of a locally bounded complex of finite locally free modules computes its derived
pullback, and the alternative (d) is preserved by composing with `f`.

`Stacks.Chow.LocalizedSituation.pullback` is an abbreviation, so that its fields reduce to
`f ≫ a`, `Z ×_X X'` and `Lf^*E` when the instances of the graph construction are synthesized.

## References

* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0GUI](https://stacks.math.columbia.edu/tag/0GUI)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

/-! ### The morphism of graph constructions over a base change -/

section GraphLift

attribute [local instance 10000] HasDerivedCategory.standard

variable {S X X' : Scheme.{u}} (a : X ⟶ S) (h : X' ⟶ X) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (E' : DerivedCategory X'.Modules)
  (hE' : RingedSpace.IsPerfect (X := X'.toRingedSpace) E')
  (e : (derivedPullback h.toLRSHom.toShHom).obj E ≅ E')

include e in
/-- **The objects of the two graph constructions pulled back to `W'` agree.** For `E' ≅ Lh^*E`,
the object `Lb'^*Lp'^*E'` of the triple of `E'` pulled back along `b' : W' ⟶ 𝐏¹_{X'}` is the object
`L(φ ∘ b')^*Lp^*E` of the triple of `E` pulled back along `W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X`. -/
theorem nonempty_derivedPullbackObject_graphTriple_iso :
    Nonempty ((graphTriple (h ≫ a) E' hE').derivedPullbackObject
        (graphBlowupToBase (h ≫ a) E' hE') ≅
      (graphTriple a E hE).derivedPullbackObject
        (graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h)) := by
  let b' := graphBlowupToBase (h ≫ a) E' hE'
  let φ := familyBaseChange a h
  let p := pullback.fst a (relativeProjectiveLine S ↘ S)
  let p' := pullback.fst (h ≫ a) (relativeProjectiveLine S ↘ S)
  have hI : ∀ Z : Scheme.{u}, (𝟭 (DerivedCategory (OXMod.{u, u} Z.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} Z.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} Z.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} Z.toRingedSpace)
          (ComplexShape.up ℤ))).functor := fun Z =>
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  have hm : (b' ≫ p') ≫ h = (b' ≫ φ) ≫ p := by
    rw [Category.assoc, Category.assoc, familyBaseChange_comp_fst]
  have e₁ : (graphTriple (h ≫ a) E' hE').derivedPullbackObject b' ≅
      (derivedPullback ((b' ≫ p') ≫ h).toLRSHom.toShHom).obj E :=
    (derivedPullback b'.toLRSHom.toShHom).mapIso ((hI _).symm.app _) ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        b'.toLRSHom.toShHom p'.toLRSHom.toShHom).app E' ≪≫
      (derivedPullback (b' ≫ p').toLRSHom.toShHom).mapIso e.symm ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (b' ≫ p').toLRSHom.toShHom h.toLRSHom.toShHom).app E
  rw [hm] at e₁
  exact ⟨e₁ ≪≫ ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (b' ≫ φ).toLRSHom.toShHom p.toLRSHom.toShHom).app E).symm ≪≫
    (derivedPullback (b' ≫ φ).toLRSHom.toShHom).mapIso ((hI _).app _)⟩

/-- The divisor at infinity of `𝐏¹_X` pulls back along `W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X` to the divisor
that the divisor at infinity of `𝐏¹_{X'}` pulls back to along `b'`. -/
theorem comap_graphTriple_comp_familyBaseChange :
    (graphTriple a E hE).D.comap (graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h) =
      (graphTriple (h ≫ a) E' hE').D.comap (graphBlowupToBase (h ≫ a) E' hE') :=
  (Scheme.IdealSheafData.comap_comp _ _ _).trans
    (congrArg (fun J => Scheme.IdealSheafData.comap J _)
      (comap_familyBaseChange_ker_infinitySection a h))

include e in
/-- **`W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X` is good for the triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`**, for `E' ≅ Lh^*E`:
it pulls the divisor at infinity back to that of `W'`, and pulls the triple back to the triple of
`E'` pulled back along `b'`, which is good by Stacks 0GTY. -/
theorem isGoodOver_graphBlowupToBase_comp_familyBaseChange :
    (graphTriple a E hE).IsGoodOver (graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h) := by
  have hb' := isGoodBlowup_graphBlowupToBase (h ≫ a) E' hE'
  have hD := comap_graphTriple_comp_familyBaseChange a h E hE E' hE'
  have hpd : Stacks.Divisors.IsPullbackDefined
      (graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h) (graphTriple a E hE).D :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hD).mpr hb'.isGoodOver.pullbackDefined
  obtain ⟨eM⟩ := nonempty_derivedPullbackObject_graphTriple_iso a h E hE E' hE' e
  exact { pullbackDefined := hpd
          isGoodTriple := ComplexAndDivisorSituation.isGoodTriple_pullback_of_comap_eq
            (graphTriple (h ≫ a) E' hE') (graphTriple a E hE) _ _ hb'.isGoodOver.pullbackDefined
            hpd hD.symm eM hb'.isGoodOver.isGoodTriple }

include e in
/-- **The graph construction of a pulled-back object maps to the graph construction** (Stacks
0GTY, 0F8V), as in the proof of Stacks 0FB3. Let `h : X' ⟶ X` be a morphism, `E` perfect on `X`
and `E' ≅ Lh^*E`, and let `b : W ⟶ 𝐏¹_X`, `Q` and `b' : W' ⟶ 𝐏¹_{X'}`, `Q'` be the graph
constructions for `E` and `E'`. Then there is a morphism `k : W' ⟶ W` with
`b ∘ k = (𝐏¹_{X'} ⟶ 𝐏¹_X) ∘ b'` and `Lk^*Q ≅ Q'`: the composite `W' ⟶ 𝐏¹_X` is good for the triple
of `E` (`Stacks.Chow.isGoodOver_graphBlowupToBase_comp_familyBaseChange`), so it factors through
`b` with `Lk^*Q` the décalage of the pulled-back triple (Stacks 0F8V, which uses Stacks 0F9X),
and that décalage is `Q'` because the two triples pulled back to `W'` agree. -/
theorem exists_lift_graphBlowupToBase_and_iso :
    ∃ k : graphBlowup (h ≫ a) E' hE' ⟶ graphBlowup a E hE,
      k ≫ graphBlowupToBase a E hE = graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h ∧
        Nonempty ((derivedPullback k.toLRSHom.toShHom).obj (graphObject a E hE) ≅
          graphObject (h ≫ a) E' hE') := by
  have hgood := isGoodOver_graphBlowupToBase_comp_familyBaseChange a h E hE E' hE' e
  obtain ⟨k, hk, ⟨e₂⟩⟩ :=
    ComplexAndDivisorSituation.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver
      (graphTriple a E hE) (graphBlowupToBase a E hE) (isGoodBlowup_graphBlowupToBase a E hE) _
      hgood
  obtain ⟨eM⟩ := nonempty_derivedPullbackObject_graphTriple_iso a h E hE E' hE' e
  obtain ⟨e₃⟩ := ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_iso_of_comap_eq
    (graphTriple a E hE) (graphTriple (h ≫ a) E' hE') _ (graphBlowupToBase (h ≫ a) E' hE')
    hgood.pullbackDefined
    (isGoodBlowup_graphBlowupToBase (h ≫ a) E' hE').isGoodOver.pullbackDefined
    (comap_graphTriple_comp_familyBaseChange a h E hE E' hE') eM.symm
  exact ⟨k, hk, ⟨e₂ ≪≫ e₃⟩⟩

end GraphLift

section PerfectLift

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W X' W' Z T T' : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]
  (h : X' ⟶ X) [LocallyOfFiniteType h] (b' : W' ⟶ projectiveLineProduct (h ≫ f)) [IsProper b']
  (hA' : IsIso (pullback.snd b' (projectiveLineAffineChart (h ≫ f)))) (k : W' ⟶ W)
  [LocallyOfFiniteType k] (hk : k ≫ b = b' ≫ familyBaseChange f h)
  (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
  (t' : T' ⟶ modificationFibreAtInfinity (h ≫ f) b') [IsClosedImmersion t']
  {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)
  {Q' : DerivedCategory W'.Modules} (hQ' : HasDefinedChernClasses Q')
  (eQ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback k.toLRSHom.toShHom).obj Q ≅ Q')
  (p : ℕ)

/-- The operation of `c'` is that of `c` through `k`, if `c'` is the restriction of `c` to `k`. -/
private theorem idRule_modification_heq_of_res_eq
    {c : TotalChowClass C (modificationProjection f b ≫ f)}
    {c' : TotalChowClass C (modificationProjection (h ≫ f) b' ≫ (h ≫ f))}
    (hres : TotalChowClass.res k (comp_modificationProjection_comp_of_lift h k hk) c = c')
    {Y : Scheme.{u}} (y : Y ⟶ W') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ k)] (k' : ℤ)
    (γ : chowGroup C (y ≫ (modificationProjection (h ≫ f) b' ≫ (h ≫ f))) k')
    (γ' : chowGroup C ((y ≫ k) ≫ (modificationProjection f b ≫ f)) k') (hγ : γ ≍ γ') :
    (c' p).idRule C _ (gysinSystemOfInvertible C) y k' γ ≍
      (c p).idRule C _ (gysinSystemOfInvertible C) (y ≫ k) k' γ' := by
  subst hres
  exact TotalChowClass.idRule_res_apply_heq k _ c p y k' γ γ' hγ

include hk eQ in
/-- **The restriction of `P'_p(Q)` along a morphism of modifications.** In the setting of
Stacks 0F9K let `h : X' ⟶ X` be locally of finite type and `Z' = Z ×_X X'`, let
`b' : W' ⟶ 𝐏¹_{X'}` be proper and an isomorphism over `𝐀¹_{X'}`, let `k : W' ⟶ W` lie over
`𝐏¹_{X'} ⟶ 𝐏¹_X`, and let `Q' ≅ Lk^*Q`. Then the class `P'_p(Q') ∈ A^p(Z' ⟶ X')` built from `b'`,
`Q'` and any closed `T' ⊆ W'_∞` with the properties of Stacks 0F9K is the restriction
(Remark 0F9Z) of `P'_p(Q) ∈ A^p(Z ⟶ X)`. This is the second and third paragraphs of the proof of
Stacks 0FB3, which combine Stacks 0GUI and the second assertion of Stacks 0FAU. -/
theorem bivariantRestriction_modificationPowerSum_of_lift
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) b' w ∉ Set.range (pullback.snd z h) →
      w ∈ Set.range t')
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t' ≫ modificationInclusionAtInfinity (h ≫ f) b').toLRSHom.toShHom).obj Q')) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (modificationPowerSum C f b hA z t hQ p hT hzero)) =
      modificationPowerSum C (h ≫ f) b' hA' (pullback.snd z h) t' hQ' p hT' hzero' := by
  refine bivariantRestriction_localizedModificationClass_of_lift z h k hk hA hA' t t' hT hT'
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p hzero)
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ' p hzero') ?_
  intro Y y _ _ k' γ γ' hγ
  exact idRule_modification_heq_of_res_eq C f b h b' k hk p
    ((res_perfectPowerSum_derivedPullback C _ hQ k _ (hQ.derivedPullback k) p).trans
      (perfectPowerSum_eq_of_iso C _ (hQ.derivedPullback k) hQ' eQ p)) y k' γ γ' hγ

include hk eQ in
/-- **The restriction of `c'_p(Q)` along a morphism of modifications.** In the setting of
Stacks 0F9K let `h : X' ⟶ X` be locally of finite type and `Z' = Z ×_X X'`, let
`b' : W' ⟶ 𝐏¹_{X'}` be proper and an isomorphism over `𝐀¹_{X'}`, let `k : W' ⟶ W` lie over
`𝐏¹_{X'} ⟶ 𝐏¹_X`, and let `Q' ≅ Lk^*Q`. Then the class `c'_p(Q') ∈ A^p(Z' ⟶ X')` built from `b'`,
`Q'` and any closed `T' ⊆ W'_∞` with the properties of Stacks 0F9K is the restriction
(Remark 0F9Z) of `c'_p(Q) ∈ A^p(Z ⟶ X)`. This is the second and third paragraphs of the proof of
Stacks 0FB3, which combine Stacks 0GUI and the second assertion of Stacks 0FAU. -/
theorem bivariantRestriction_modificationChernClass_of_lift
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) b' w ∉ Set.range (pullback.snd z h) →
      w ∈ Set.range t')
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank' : ∃ M : T'.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t' ≫ modificationInclusionAtInfinity (h ≫ f) b').toLRSHom.toShHom).obj Q' ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (modificationChernClass C f b hA z t hQ p hT hrank)) =
      modificationChernClass C (h ≫ f) b' hA' (pullback.snd z h) t' hQ' p hT' hrank' := by
  refine bivariantRestriction_localizedModificationClass_of_lift z h k hk hA hA' t t' hT hT'
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p hrank)
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ' p hrank') ?_
  intro Y y _ _ k' γ γ' hγ
  exact idRule_modification_heq_of_res_eq C f b h b' k hk p
    ((res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ k _ (hQ.derivedPullback k)).trans
      (perfectChernClass_congr C _ (hQ.derivedPullback k) hQ' eQ)) y k' γ γ' hγ

end PerfectLift

/-! ### The classes of the graph construction -/

section Graph

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X X' Z T T' : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (h : X' ⟶ X) [LocallyOfFiniteType h] (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (E' : DerivedCategory X'.Modules)
  (hE' : RingedSpace.IsPerfect (X := X'.toRingedSpace) E') (z : Z ⟶ X) [IsClosedImmersion z]
  (k : graphBlowup (h ≫ a) E' hE' ⟶ graphBlowup a E hE)
  (hk : k ≫ graphBlowupToBase a E hE = graphBlowupToBase (h ≫ a) E' hE' ≫ familyBaseChange a h)
  (eQ : (derivedPullback k.toLRSHom.toShHom).obj (graphObject a E hE) ≅ graphObject (h ≫ a) E' hE')
  (t : T ⟶ modificationFibreAtInfinity a (graphBlowupToBase a E hE)) [IsClosedImmersion t]
  (t' : T' ⟶ modificationFibreAtInfinity (h ≫ a) (graphBlowupToBase (h ≫ a) E' hE'))
  [IsClosedImmersion t']
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology a E hE t n))
  (hH' : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology (h ≫ a) E' hE' t' n))
  (hQ : HasDefinedChernClasses (graphObject a E hE))
  (hQ' : HasDefinedChernClasses (graphObject (h ≫ a) E' hE')) (p : ℕ)
  (hT : ∀ w, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) w ∉ Set.range z →
    w ∈ Set.range t)
  (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ a) (graphBlowupToBase (h ≫ a) E' hE') w ∉
    Set.range (pullback.snd z h) → w ∈ Set.range t')

include hk in
/-- A morphism of graph constructions over `𝐏¹_{X'} ⟶ 𝐏¹_X` is locally of finite type. -/
theorem locallyOfFiniteType_of_comp_graphBlowupToBase : LocallyOfFiniteType k := by
  have : LocallyOfFiniteType
      (k ≫ (modificationProjection a (graphBlowupToBase a E hE) ≫ a)) := by
    rw [← Category.assoc, comp_modificationProjection_of_lift h k hk, Category.assoc]
    infer_instance
  exact locallyOfFiniteType_of_comp k (modificationProjection a (graphBlowupToBase a E hE) ≫ a)

include hk eQ in
/-- **The restriction of `P_p(Z ⟶ X, E)` along `h : X' ⟶ X`, given the identification of the
graph constructions.** Let `E' ≅ Lh^*E`, let `k : W' ⟶ W` be a morphism of the graph
constructions over `𝐏¹_{X'} ⟶ 𝐏¹_X` and let `Q' ≅ Lk^*Q`. Then the class `P_p(Z' ⟶ X', E')`
attached to any closed subscheme `T' ⊆ W'_∞` with the properties of Stacks 0F90 (3), (4) is the
restriction (Remark 0F9Z) of the class `P_p(Z ⟶ X, E)` attached to `T ⊆ W_∞`. -/
theorem bivariantRestriction_graphPowerSumClass_of_iso
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity (h ≫ a)
      (graphBlowupToBase (h ≫ a) E' hE') (t' τ) ∉ Set.range (pullback.snd z h) →
        ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ a) a z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (graphPowerSumClass C a E hE z t hH hQ p hT hrk)) =
      graphPowerSumClass C (h ≫ a) E' hE' (pullback.snd z h) t' hH' hQ' p hT' hrk' := by
  have := locallyOfFiniteType_of_comp_graphBlowupToBase C a h E hE E' hE' k hk
  exact bivariantRestriction_modificationPowerSum_of_lift C a _ _ z h _ _ k hk _ _ hQ hQ' eQ p _
    _ _ _

include hk eQ in
/-- **The restriction of `c_p(Z ⟶ X, E)` along `h : X' ⟶ X`, given the identification of the
graph constructions.** Let `E' ≅ Lh^*E`, let `k : W' ⟶ W` be a morphism of the graph
constructions over `𝐏¹_{X'} ⟶ 𝐏¹_X` and let `Q' ≅ Lk^*Q`. Then the class `c_p(Z' ⟶ X', E')`
attached to any closed subscheme `T' ⊆ W'_∞` with the properties of Stacks 0F90 (3), (4) is the
restriction (Remark 0F9Z) of the class `c_p(Z ⟶ X, E)` attached to `T ⊆ W_∞`. -/
theorem bivariantRestriction_graphChernClass_of_iso
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity (h ≫ a)
      (graphBlowupToBase (h ≫ a) E' hE') (t' τ) ∉ Set.range (pullback.snd z h) →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' 0) τ < p) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ a) a z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (graphChernClass C a E hE z t hH hQ p hT hrk)) =
      graphChernClass C (h ≫ a) E' hE' (pullback.snd z h) t' hH' hQ' p hT' hrk' := by
  have := locallyOfFiniteType_of_comp_graphBlowupToBase C a h E hE E' hE' k hk
  exact bivariantRestriction_modificationChernClass_of_lift C a _ _ z h _ _ k hk _ _ hQ hQ' eQ p
    _ _ _ _

end Graph

/-! ### The pulled-back situation -/

section Square

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A finite locally free module of rank `< p` restricts along a commutative square.** If
`a ≫ i = b ≫ j` and `E|_Z` along `i : Z ⟶ X` is a finite locally free module of rank `< p` placed
in degree `0`, so is the restriction `(E|_Y)|_V` along `j : Y ⟶ X` and then `b : V ⟶ Y`. -/
theorem exists_pullback_isFiniteLocallyFreeOfRankLT_of_comp_eq {V X Y Z : Scheme.{u}}
    {i : Z ⟶ X} {j : Y ⟶ X} {a : V ⟶ Z} {b : V ⟶ Y} (h : a ≫ i = b ≫ j)
    {E : DerivedCategory X.Modules} {p : ℕ}
    (hrank : ∃ M : Z.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : V.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        b.toLRSHom.toShHom).obj ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          j.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors h hrank
  exact ⟨N, hN, ⟨derivedPullbackCompIsoOfScheme b j E ≪≫ e⟩⟩

end Square

namespace LocalizedChernData

attribute [local instance 10000] HasDerivedCategory.standard

variable (D : LocalizedChernData.{u}) {X' : Scheme.{u}} (f : X' ⟶ D.X)

/-- The complement `X' ∖ Z'` of `Z' = Z ×_X X'` maps into `X ∖ Z` under `f : X' ⟶ X`. -/
theorem range_compl_pullbackSnd_subset :
    Set.range (Scheme.Opens.ι (⟨(Set.range (pullback.snd D.i f).base)ᶜ,
      (pullback.snd D.i f).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X'.Opens) ≫ f) ⊆
      Set.range (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) := by
  have key : ∀ y : X', f y ∈ Set.range D.i → y ∈ Set.range (pullback.snd D.i f) := by
    intro y hy
    rw [Scheme.Pullback.range_snd]
    exact hy
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact fun hz => x.2 (key _ hz)

/-- **Condition (2) of Situation 0GUJ is stable under base change**: if `E|_{X ∖ Z}` is zero,
resp. finite locally free of rank `< p` in degree `0`, then so is `(Lf^*E)|_{X' ∖ Z'}` for
`Z' = Z ×_X X'`, because `X' ∖ Z' ⟶ X'` followed by `f` factors through `X ∖ Z`. -/
theorem restriction_pullback :
    letI U : TopologicalSpace.Opens X' :=
      ⟨(Set.range (pullback.snd D.i f).base)ᶜ,
        (pullback.snd D.i f).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X'.toRingedSpace.ofRestrict U.isOpenEmbedding)
    IsZero (F.obj ((derivedPullback f.toLRSHom.toShHom).obj D.E)) ∨
      ∃ M : OXMod.{u, u, u} (X'.toRingedSpace.restrict U.isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M D.p ∧
          Nonempty (F.obj ((derivedPullback f.toLRSHom.toShHom).obj D.E) ≅
            (DerivedCategory.singleFunctor _ 0).obj M) :=
  D.restriction.imp
    (fun h => isZero_derivedPullback_of_isZero_of_comp_eq
      (i := Scheme.Opens.ι _) (b := Scheme.Opens.ι _)
      (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset f)) h)
    (fun h => exists_pullback_isFiniteLocallyFreeOfRankLT_of_comp_eq
      (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset f)) h)

variable [LocallyOfFiniteType f]

/-- **The base change of the data of a localized Chern class** along a morphism
`f : X' ⟶ X` locally of finite type: the scheme `X'`, the closed subscheme `Z ×_X X'`, the
object `Lf^*E` and the same degree. -/
abbrev pullback : LocalizedChernData.{u} where
  base := D.base
  X := X'
  a := f ≫ D.a
  Z := Limits.pullback D.i f
  i := Limits.pullback.snd D.i f
  E := (derivedPullback f.toLRSHom.toShHom).obj D.E
  p := D.p
  perfect := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ D.perfect
  restriction := D.restriction_pullback f

variable {D f}

/-- If `E|_{X ∖ Z}` is zero, so is `(Lf^*E)|_{X' ∖ Z'}`. -/
theorem IsZeroOnComplement.pullback (h : D.IsZeroOnComplement) :
    (D.pullback f).IsZeroOnComplement :=
  isZero_derivedPullback_of_isZero_of_comp_eq (i := Scheme.Opens.ι _) (b := Scheme.Opens.ι _)
    (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset f)) h

/-- If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, so is
`(Lf^*E)|_{X' ∖ Z'}`. -/
theorem IsFiniteLocallyFreeOfRankLTOnComplement.pullback
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    (D.pullback f).IsFiniteLocallyFreeOfRankLTOnComplement :=
  exists_pullback_isFiniteLocallyFreeOfRankLT_of_comp_eq
    (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset f)) h

end LocalizedChernData

namespace LocalizedSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : LocalizedSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ S.X)
  [LocallyOfFiniteType f]

omit [LocallyOfFiniteType f] in
/-- **Condition (3) of Situation 0GUJ is stable under base change**: the alternatives (a) and
(b) for `X` give the alternative (d) for `X'` (through `f`), and the alternatives (c) and (d) for
`X` give the same alternative for `X'`. -/
theorem finiteness_pullback :
    CompactSpace X' ∨
      (∀ C ∈ irreducibleComponents X', IsCompact C) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X'.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧
          Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj S.E)) ∨
      (∃ (X'' : Scheme.{u}) (a'' : X'' ⟶ S.base.S) (g : X' ⟶ X'')
          (E'' : DerivedCategory (OXMod.{u, u, u} X''.toRingedSpace)),
        LocallyOfFiniteType a'' ∧ g ≫ a'' = f ≫ S.a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X''.toRingedSpace) E'' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            g.toLRSHom.toShHom).obj E'' ≅ (derivedPullback f.toLRSHom.toShHom).obj S.E) ∧
          ∀ C ∈ irreducibleComponents X'', IsCompact C) := by
  by_cases hX : ∀ C ∈ irreducibleComponents S.X, IsCompact C
  · exact Or.inr (Or.inr (Or.inr ⟨S.X, S.a, f, S.E, inferInstance, rfl, S.perfect, ⟨Iso.refl _⟩,
      hX⟩))
  rcases S.finiteness with hc | hc | ⟨P, hP, ⟨e⟩⟩ | ⟨X'', a'', g, E'', ha'', hg, hE'', ⟨e⟩, hX''⟩
  · exact (hX fun C hC => (isClosed_of_mem_irreducibleComponents C hC).isCompact).elim
  · exact (hX hc).elim
  · refine Or.inr (Or.inr (Or.inl ⟨pullbackComplex f P,
      Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback f P hP, ?_⟩))
    exact ⟨(Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom P
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P hP)).symm ≪≫
        (derivedPullback f.toLRSHom.toShHom).mapIso e⟩
  · exact Or.inr (Or.inr (Or.inr ⟨X'', a'', f ≫ g, E'', ha'', by rw [Category.assoc, hg], hE'',
      ⟨(derivedPullbackCompIsoOfScheme f g E'').symm ≪≫
        (derivedPullback f.toLRSHom.toShHom).mapIso e⟩, hX''⟩))

/-- **The base change of Situation 0GUJ** along a morphism `f : X' ⟶ X` locally of finite type:
the scheme `X'`, the closed subscheme `Z' = Z ×_X X'`, the object `E' = Lf^*E` and the same
degree `p`. Conditions (2) and (3) are `Stacks.Chow.LocalizedChernData.restriction_pullback`
and `Stacks.Chow.LocalizedSituation.finiteness_pullback`. -/
abbrev pullback : LocalizedSituation.{u} where
  base := S.base
  X := X'
  a := f ≫ S.a
  Z := Limits.pullback S.i f
  i := Limits.pullback.snd S.i f
  E := (derivedPullback f.toLRSHom.toShHom).obj S.E
  p := S.p
  perfect := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ S.perfect
  restriction := S.restriction_pullback f
  finiteness := S.finiteness_pullback f

variable {S f}

/-- If `E|_{X ∖ Z}` is zero, so is `(Lf^*E)|_{X' ∖ Z'}`. -/
theorem IsZeroOnComplement.pullback (h : S.IsZeroOnComplement) :
    (S.pullback f).IsZeroOnComplement :=
  LocalizedChernData.IsZeroOnComplement.pullback h

/-- If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, so is
`(Lf^*E)|_{X' ∖ Z'}`. -/
theorem IsFiniteLocallyFreeOfRankLTOnComplement.pullback
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    (S.pullback f).IsFiniteLocallyFreeOfRankLTOnComplement :=
  LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback h

variable (f) in
/-- In Situation 0GUJ with `E|_{X ∖ Z}` zero, let `f : X' ⟶ X` be
locally of finite type, `E' = Lf^*E` and `Z' = f^{-1}(Z) = Z ×_X X'`. Then the class
`P_p(Z' ⟶ X', E') ∈ A^p(Z' ⟶ X')` of Stacks 0FB2, constructed from `X'`, `Z'`, `E'` (the
situation `Stacks.Chow.LocalizedSituation.pullback`), is the restriction (Remark 0F9Z) of
`P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`. -/
@[stacks 0FB3 "for P_p: the class P_p(Z' → X', E') of Lemma 0FB2 for X', Z' = f^{-1}(Z) and \
E' = f^*E is the restriction (Remark 0F9Z) of P_p(Z → X, E)"]
theorem bivariantRestriction_localizedPowerSum (h : S.IsZeroOnComplement) (p : ℕ) :
    bivariantClassCongrBase S.base (gysinSystemOfInvertible S.base) (Limits.pullback.snd S.i f)
        (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl f).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl f)
        (hv' := rfl) p
        (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl f p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
          (S.localizedPowerSum h p)) =
      (S.pullback f).localizedPowerSum h.pullback p := by
  obtain ⟨k, hk, ⟨eQ⟩⟩ :=
    exists_lift_graphBlowupToBase_and_iso S.a f S.E S.perfect _ (S.pullback f).perfect (Iso.refl _)
  exact bivariantRestriction_graphPowerSumClass_of_iso S.base S.a f S.E S.perfect _ _ S.i k hk eQ
    S.graphSubschemeι (S.pullback f).graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
    (S.pullback f).isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject (S.pullback f).hasDefinedChernClasses_graphObject p
    S.mem_range_graphSubschemeι (S.pullback f).mem_range_graphSubschemeι
    (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h)
    ((S.pullback f).finiteLocallyFreeRank_graphSubscheme_eq_zero h.pullback)

variable (f) in
/-- In Situation 0GUJ with `E|_{X ∖ Z}` finite locally free of rank
`< p` in degree `0`, let `f : X' ⟶ X` be locally of finite type, `E' = Lf^*E` and
`Z' = f^{-1}(Z) = Z ×_X X'`. Then the class `c_p(Z' ⟶ X', E') ∈ A^p(Z' ⟶ X')` of Stacks 0FB2,
constructed from `X'`, `Z'`, `E'` (the situation `Stacks.Chow.LocalizedSituation.pullback`),
is the restriction (Remark 0F9Z) of `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`. -/
@[stacks 0FB3 "for c_p: the class c_p(Z' → X', E') of Lemma 0FB2 for X', Z' = f^{-1}(Z) and \
E' = f^*E is the restriction (Remark 0F9Z) of c_p(Z → X, E)"]
theorem bivariantRestriction_localizedChern (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantClassCongrBase S.base (gysinSystemOfInvertible S.base) (Limits.pullback.snd S.i f)
        (pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl f).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq S.base (S.i ≫ S.a) S.a S.i rfl f)
        (hv' := rfl) S.p
        (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl f
          S.p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
          (S.localizedChern h)) =
      (S.pullback f).localizedChern h.pullback := by
  obtain ⟨k, hk, ⟨eQ⟩⟩ :=
    exists_lift_graphBlowupToBase_and_iso S.a f S.E S.perfect _ (S.pullback f).perfect (Iso.refl _)
  exact bivariantRestriction_graphChernClass_of_iso S.base S.a f S.E S.perfect _ _ S.i k hk eQ
    S.graphSubschemeι (S.pullback f).graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
    (S.pullback f).isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject (S.pullback f).hasDefinedChernClasses_graphObject S.p
    S.mem_range_graphSubschemeι (S.pullback f).mem_range_graphSubschemeι
    (S.finiteLocallyFreeRank_graphSubscheme_lt h)
    ((S.pullback f).finiteLocallyFreeRank_graphSubscheme_lt h.pullback)

end LocalizedSituation

end Stacks.Chow

end
