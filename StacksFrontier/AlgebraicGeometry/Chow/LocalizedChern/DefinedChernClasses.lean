module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence

/-!
# Localized Chern classes of an object whose Chern classes are defined

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`, let
`i : Z ⟶ X` be a closed immersion and let `E ∈ D(𝒪_X)` be perfect with `E|_{X ∖ Z}` zero,
resp. finite locally free of rank `< p` in degree `0` (conditions (1) and (2) of Situation 0GUJ,
the structure `Stacks.Chow.LocalizedChernData`). Remark 0GUK observes that the finiteness
condition (3) of Situation 0GUJ may be replaced by the assumption that the Chern classes of `E`
are defined (Stacks 0F9E), combining Stacks 0FB2, 0FB3 and 0GUC. This file carries this out.

Choose an envelope `g : Y ⟶ X` on which `Lg^*E` is represented by a locally bounded complex of
finite locally free modules. The base change `(Y, Z ×_X Y, Lg^*E)` is an instance of
Situation 0GUJ through alternative (c) of condition (3), so Stacks 0FB2 gives
`P_p(Z ×_X Y ⟶ Y, Lg^*E)`, resp. `c_p(Z ×_X Y ⟶ Y, Lg^*E)`. By Stacks 0FB3 its two restrictions to
`Y ×_X Y` are both the class of the pullback of `E` to `Y ×_X Y`, so by Stacks 0GUC there is a
unique class

  `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`,   resp.   `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)`

restricting to it. In Situation 0GUJ this is the class of Stacks 0FB2: the class of Stacks 0FB2
restricts along `g` to the class upstairs by Stacks 0FB3, and the uniqueness in Stacks 0GUC
applies.

## Main definitions

* `Stacks.Chow.LocalizedChernData.envelopeSituation` — the instance of Situation 0GUJ over an
  envelope presentation of `E`.
* `Stacks.Chow.LocalizedChernData.localizedPowerSum`,
  `Stacks.Chow.LocalizedChernData.localizedChern`,
  `Stacks.Chow.LocalizedChernData.localizedChernChar` — `P_p(Z ⟶ X, E)`, `c_p(Z ⟶ X, E)` and
  `ch(Z ⟶ X, E)` when the Chern classes of `E` are defined (Remark 0GUK).

## Main results

* `Stacks.Chow.LocalizedChernData.envelopeDescentRes₁_envelopePowerSum`,
  `Stacks.Chow.LocalizedChernData.envelopeDescentRes₁_envelopeChern` — the descent condition of
  Stacks 0GUC for the classes over an envelope.
* `Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedPowerSum_envelope`,
  `Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedChern_envelope` — the classes
  restrict to the classes of Stacks 0FB2 along the envelope of every presentation of `E`, so they
  do not depend on the presentation chosen.
* `Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum`,
  `Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern` —
  the same along any envelope on which `E` is represented by a locally bounded complex of finite
  locally free modules, the source read over the base through the envelope.
* `Stacks.Chow.bivariantTransport_bivariantRestriction_bivariantRestriction` — restriction along
  a composite is the iterated restriction (Remark 0F9Z), at the level of classes.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`,
  `Stacks.Chow.LocalizedSituation.localizedChern_toLocalizedChernData` — in Situation 0GUJ
  the classes are those of Stacks 0FB2.
* `Stacks.Chow.bivariantTransport_bivariantRestriction_graphPowerSumClass`,
  `Stacks.Chow.bivariantTransport_bivariantRestriction_graphChernClass` — the restriction of the
  class of the graph construction, read on any closed subscheme identified with `Z ×_X X'`.

## Implementation notes

The class is defined through the presentation chosen by `HasDefinedChernClasses`; by the
uniqueness in Stacks 0GUC and Stacks 0FB3 it restricts along the envelope of every presentation to
the class of Stacks 0FB2 upstairs
(`Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedPowerSum_envelope`), so it does not
depend on the choice. In Situation 0GUJ the two
constructions agree by `Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`;
the statements of Stacks 0FB2 are registered on the classes of the situation.

## References

* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section TransportPushforward

/-- A class read for equal structure morphisms (`Stacks.Chow.bivariantClassCongrBase`) is
heterogeneously equal to the class. -/
theorem bivariantClassCongrBase_heq {C : ChowSituation.{u}} {G : GysinSystem C} {A W : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sW sW' : W ⟶ C.S} [LocallyOfFiniteType sW] [LocallyOfFiniteType sW']
    (v : A ⟶ W) [LocallyOfFiniteType v] (hsA : sA = sA') (hsW : sW = sW')
    {hv : v ≫ sW = sA} {hv' : v ≫ sW' = sA'} (p : ℤ) (c : BivariantClass C G sA sW v hv p) :
    bivariantClassCongrBase C G v hsA hsW (hv := hv) (hv' := hv') p c ≍ c := by
  subst hsA hsW
  rfl

variable {C : ChowSituation.{u}} {A B W : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
  {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sW : W ⟶ C.S} [LocallyOfFiniteType sW]
  {v : A ⟶ W} [LocallyOfFiniteType v] {u : B ⟶ W} [LocallyOfFiniteType u] {p : ℤ}

/-- **Transport along an isomorphism of sources is proper pushforward along it**
(`Stacks.Chow.bivariantTransport_eq_bivariantProperPushforward`), for a class given only up to
heterogeneous equality and with an arbitrary structure morphism of the source. -/
theorem bivariantTransport_eq_bivariantProperPushforward_of_eq (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
    (hv : v ≫ sW = sA) (hu : u ≫ sW = sB) {sA' : A ⟶ C.S} [LocallyOfFiniteType sA']
    (hθB : θ.hom ≫ sB = sA')
    (c : BivariantClass C (gysinSystemOfInvertible C) sA sW v hv p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sA' sW (θ.hom ≫ u)
      (comp_comp_structureMorphism_eq hθB hu) p)
    (hc : c' ≍ c) :
    bivariantTransport C (gysinSystemOfInvertible C) sA sB sW v hv u hu θ hθ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      bivariantProperPushforwardOfInvertible C sA' sB sW θ.hom u hθB hu p c' := by
  have hsA : sA' = sA := by rw [← hθB, ← hu, ← Category.assoc, hθ, hv]
  subst hθ hv hsA
  obtain rfl := eq_of_heq hc
  exact bivariantTransport_eq_bivariantProperPushforward θ hu _

end TransportPushforward

/-- A condition on the points of a space away from a set `s` holds away from an equal set `s'`. -/
private theorem forall_notMem_of_eq {α β : Type*} {s s' : Set β} (hs : s' = s) {g : α → β}
    {R : α → Prop} (h : ∀ x, g x ∉ s → R x) : ∀ x, g x ∉ s' → R x :=
  hs ▸ h

section Graph

variable (C : ChowSituation.{u}) {X X' Z Z' T T' : Scheme.{u}} (a : X ⟶ C.S)
  [LocallyOfFiniteType a] (h : X' ⟶ X) [LocallyOfFiniteType h] (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (E' : DerivedCategory X'.Modules)
  (hE' : RingedSpace.IsPerfect (X := X'.toRingedSpace) E')
  (e : (derivedPullback h.toLRSHom.toShHom).obj E ≅ E')
  (z : Z ⟶ X) [IsClosedImmersion z] (z' : Z' ⟶ X') [IsClosedImmersion z']
  (θ : pullback z h ≅ Z') (hθ : θ.hom ≫ z' = pullback.snd z h)
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
    Set.range z' → w ∈ Set.range t')

omit [LocallyOfFiniteType h] [IsClosedImmersion z] [IsClosedImmersion z'] in
include hθ in
/-- Two closed subschemes of `X'` identified over `X'` have the same underlying set. -/
theorem range_eq_range_pullbackSnd_of_iso : Set.range z' = Set.range (pullback.snd z h) := by
  have hθ' : θ.inv ≫ pullback.snd z h = z' := by rw [← hθ, Iso.inv_hom_id_assoc]
  apply subset_antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨θ.inv y, by rw [← Scheme.Hom.comp_apply, hθ']⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨θ.hom y, by rw [← Scheme.Hom.comp_apply, hθ]⟩

include e hθ in
/-- **The restriction of `P_p(Z ⟶ X, E)` along `h : X' ⟶ X`, read on a closed subscheme
identified with `Z ×_X X'`.** Let `E' ≅ Lh^*E`, and let `z' : Z' ⟶ X'` be a closed immersion with
an isomorphism `θ : Z ×_X X' ≅ Z'` over `X'`. Then the restriction (Remark 0F9Z) of the class of
the graph construction of `E` for `Z`, transported along `θ`, is the class of the graph
construction of `E'` for `Z'`: by Stacks 0FB3 it is the class for `Z ×_X X'`, and by
Stacks 0FB7 for the isomorphism `θ` the transport along `θ` takes it to the class for `Z'`. -/
theorem bivariantTransport_bivariantRestriction_graphPowerSumClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity (h ≫ a)
      (graphBlowupToBase (h ≫ a) E' hE') (t' τ) ∉ Set.range z' →
        ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z h ≫ (z ≫ a)) (z' ≫ (h ≫ a))
        (h ≫ a) (pullback.snd z h) (pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h)
        z' rfl θ hθ p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ a) a z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (graphPowerSumClass C a E hE z t hH hQ p hT hrk)) =
      graphPowerSumClass C (h ≫ a) E' hE' z' t' hH' hQ' p hT' hrk' := by
  have hR := range_eq_range_pullbackSnd_of_iso h z z' θ hθ
  have hT'' := forall_notMem_of_eq hR.symm hT'
  have hrk'' := forall_notMem_of_eq hR.symm hrk'
  obtain ⟨k, hk, ⟨eQ⟩⟩ := exists_lift_graphBlowupToBase_and_iso a h E hE E' hE' e
  have key := bivariantRestriction_graphPowerSumClass_of_iso C a h E hE E' hE' z k hk eQ t t'
    hH hH' hQ hQ' p hT hT'' hrk hrk''
  have fb7 := graphPowerSumClass_eq_bivariantProperPushforward C (h ≫ a) E' hE' θ.hom hθ t' hH'
    hQ' p hT'' hrk''
  refine Eq.trans ?_ fb7.symm
  apply bivariantTransport_eq_bivariantProperPushforward_of_eq
  refine (BivariantClass.congrHom_heq _ _ _).trans ?_
  rw [← key]
  exact bivariantClassCongrBase_heq _ _ _ _ _

include e hθ in
/-- `Stacks.Chow.bivariantTransport_bivariantRestriction_graphPowerSumClass`, with the structure
morphisms of `Z`, `Z'` and `X'` given by equalities, as they arise from the descent condition of
Stacks 0GUC. -/
theorem bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (hz : z ≫ a = sZ)
    {sB : Z' ⟶ C.S} [LocallyOfFiniteType sB] (a' : X' ⟶ C.S) [LocallyOfFiniteType a']
    (ha' : h ≫ a = a') (hsB : z' ≫ a' = sB)
    {T'' : Scheme.{u}} (t'' : T'' ⟶ modificationFibreAtInfinity a' (graphBlowupToBase a' E' hE'))
    [IsClosedImmersion t'']
    (hH'' : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (graphObjectRestrictHomology a' E' hE' t'' n))
    (hQ'' : HasDefinedChernClasses (graphObject a' E' hE'))
    (hT'' : ∀ w, modificationProjectionAtInfinity a' (graphBlowupToBase a' E' hE') w ∉
      Set.range z' → w ∈ Set.range t'')
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0)
    (hrk'' : ∀ τ : T'', modificationProjectionAtInfinity a'
      (graphBlowupToBase a' E' hE') (t'' τ) ∉ Set.range z' →
        ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T'' _ (hH'' n) τ = 0) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z h ≫ sZ) sB
        (h ≫ a) (pullback.snd z h) (pullbackSnd_comp_structureMorphism_eq C sZ a z hz h)
        z' (by rw [← hsB, ha']) θ hθ p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ a z hz h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (bivariantClassCongrBase C (gysinSystemOfInvertible C) z hz rfl (hv := rfl) (hv' := hz)
            p (graphPowerSumClass C a E hE z t hH hQ p hT hrk))) =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) z' hsB ha'.symm (hv := rfl)
        (hv' := by rw [← hsB, ha']) p
        (graphPowerSumClass C a' E' hE' z' t'' hH'' hQ'' p hT'' hrk'') := by
  subst hz ha' hsB
  exact bivariantTransport_bivariantRestriction_graphPowerSumClass C a h E hE E' hE' e z z' θ hθ
    t t'' hH hH'' hQ hQ'' p hT hT'' hrk hrk''

include e hθ in
/-- **The restriction of `c_p(Z ⟶ X, E)` along `h : X' ⟶ X`, read on a closed subscheme
identified with `Z ×_X X'`.** As
`Stacks.Chow.bivariantTransport_bivariantRestriction_graphPowerSumClass`, for the classes
`Stacks.Chow.graphChernClass`. -/
theorem bivariantTransport_bivariantRestriction_graphChernClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p)
    (hrk' : ∀ τ : T', modificationProjectionAtInfinity (h ≫ a)
      (graphBlowupToBase (h ≫ a) E' hE') (t' τ) ∉ Set.range z' →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T' _ (hH' 0) τ < p) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z h ≫ (z ≫ a)) (z' ≫ (h ≫ a))
        (h ≫ a) (pullback.snd z h) (pullbackSnd_comp_structureMorphism_eq C (z ≫ a) a z rfl h)
        z' rfl θ hθ p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ a) a z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (graphChernClass C a E hE z t hH hQ p hT hrk)) =
      graphChernClass C (h ≫ a) E' hE' z' t' hH' hQ' p hT' hrk' := by
  have hR := range_eq_range_pullbackSnd_of_iso h z z' θ hθ
  have hT'' := forall_notMem_of_eq hR.symm hT'
  have hrk'' := forall_notMem_of_eq hR.symm hrk'
  obtain ⟨k, hk, ⟨eQ⟩⟩ := exists_lift_graphBlowupToBase_and_iso a h E hE E' hE' e
  have key := bivariantRestriction_graphChernClass_of_iso C a h E hE E' hE' z k hk eQ t t'
    hH hH' hQ hQ' p hT hT'' hrk hrk''
  have fb7 := graphChernClass_eq_bivariantProperPushforward C (h ≫ a) E' hE' θ.hom hθ t' hH'
    hQ' p hT'' hrk''
  refine Eq.trans ?_ fb7.symm
  apply bivariantTransport_eq_bivariantProperPushforward_of_eq
  refine (BivariantClass.congrHom_heq _ _ _).trans ?_
  rw [← key]
  exact bivariantClassCongrBase_heq _ _ _ _ _

include e hθ in
/-- `Stacks.Chow.bivariantTransport_bivariantRestriction_graphChernClass`, with the structure
morphisms of `Z`, `Z'` and `X'` given by equalities. -/
theorem bivariantTransport_bivariantRestriction_graphChernClass_of_eq
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (hz : z ≫ a = sZ)
    {sB : Z' ⟶ C.S} [LocallyOfFiniteType sB] (a' : X' ⟶ C.S) [LocallyOfFiniteType a']
    (ha' : h ≫ a = a') (hsB : z' ≫ a' = sB)
    {T'' : Scheme.{u}} (t'' : T'' ⟶ modificationFibreAtInfinity a' (graphBlowupToBase a' E' hE'))
    [IsClosedImmersion t'']
    (hH'' : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (graphObjectRestrictHomology a' E' hE' t'' n))
    (hQ'' : HasDefinedChernClasses (graphObject a' E' hE'))
    (hT'' : ∀ w, modificationProjectionAtInfinity a' (graphBlowupToBase a' E' hE') w ∉
      Set.range z' → w ∈ Set.range t'')
    (hrk : ∀ τ : T, modificationProjectionAtInfinity a (graphBlowupToBase a E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p)
    (hrk'' : ∀ τ : T'', modificationProjectionAtInfinity a'
      (graphBlowupToBase a' E' hE') (t'' τ) ∉ Set.range z' →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T'' _ (hH'' n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T'' _ (hH'' 0) τ < p) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z h ≫ sZ) sB
        (h ≫ a) (pullback.snd z h) (pullbackSnd_comp_structureMorphism_eq C sZ a z hz h)
        z' (by rw [← hsB, ha']) θ hθ p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ a z hz h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (bivariantClassCongrBase C (gysinSystemOfInvertible C) z hz rfl (hv := rfl) (hv' := hz)
            p (graphChernClass C a E hE z t hH hQ p hT hrk))) =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) z' hsB ha'.symm (hv := rfl)
        (hv' := by rw [← hsB, ha']) p
        (graphChernClass C a' E' hE' z' t'' hH'' hQ'' p hT'' hrk'') := by
  subst hz ha' hsB
  exact bivariantTransport_bivariantRestriction_graphChernClass C a h E hE E' hE' e z z' θ hθ
    t t'' hH hH'' hQ hQ'' p hT hT'' hrk hrk''

end Graph

/-- A class read against an equal structure morphism of the target
(`Stacks.Chow.BivariantClass.congrBase`) is heterogeneously equal to the class. -/
theorem BivariantClass.congrBase_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p : ℤ} (h : sY = sY') (hf' : f ≫ sY' = sX)
    (c : BivariantClass C G sX sY f hf p) : c.congrBase h hf' ≍ c := by
  subst h
  rfl

section TransportRestriction

variable (C : ChowSituation.{u}) (G : GysinSystem C)

/-- **Transport along an isomorphism of sources is injective**: the cap operations of the
transport are those of the class, pushed forward along isomorphisms of the base changes. -/
theorem bivariantTransport_injective {A B W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W) [LocallyOfFiniteType u]
    (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (p : ℤ)
    (hgys : G.IsNaturalUnderBaseChangeIso) :
    Function.Injective (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys) := by
  intro c d hcd
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  have key := congrArg (fun e : BivariantClass C G sB sW u hu p ↦ e.cap t k α) hcd
  simp only [bivariantTransport_cap, bivariantTransportCap_apply] at key
  exact chowPushforwardOfIso_injective C _ _ _ _ _ key

variable {X Y Y' Y'' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- **Restriction along a composite is the iterated restriction** (Remark 0F9Z), at the level of
classes: for `h : Y' ⟶ Y`, `h' : Y'' ⟶ Y'` and any morphism `m : Y'' ⟶ Y` equal to `h' ≫ h`,
the restriction of `c` along `h` and then along `h'`,
transported along the canonical isomorphism `(X ×_Y Y') ×_{Y'} Y'' ≅ X ×_Y Y''`, is the
restriction of `c` along `m`. -/
theorem bivariantTransport_bivariantRestriction_bivariantRestriction
    (hgys : G.IsNaturalUnderBaseChangeIso) (c : BivariantClass C G sX sY f hf p) (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] (h' : Y'' ⟶ Y') [LocallyOfFiniteType h'] (m : Y'' ⟶ Y)
    [LocallyOfFiniteType m] (hm : h' ≫ h = m) :
    bivariantTransport C G (pullback.fst (pullback.snd f h) h' ≫ (pullback.fst f h ≫ sX))
        (pullback.fst f m ≫ sX) (h' ≫ (h ≫ sY)) (pullback.snd (pullback.snd f h) h')
        (pullbackSnd_comp_structureMorphism_eq C _ _ _
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) h')
        (pullback.snd f m) (by rw [← hm, ← Category.assoc h' h sY]; exact
          pullbackSnd_comp_structureMorphism_eq C sX sY f hf (h' ≫ h))
        (pullbackLeftPullbackSndIso f h h' ≪≫ pullback.congrHom rfl hm) (by subst hm; simp) p
        hgys
        (bivariantRestriction C G _ _ _ _ h' p hgys
          (bivariantRestriction C G sX sY f hf h p hgys c)) =
      (bivariantRestriction C G sX sY f hf m p hgys c).congrBase
        (by rw [← hm, Category.assoc]) (by rw [← hm, ← Category.assoc h' h sY]; exact
          pullbackSnd_comp_structureMorphism_eq C sX sY f hf (h' ≫ h)) := by
  subst hm
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply, BivariantClass.congrBase_cap,
    ← bivariantRestriction_comp C G sX sY f hf h p h' hgys c t k α]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [transportPullbackIso, iteratedRestrictionIso, pullback.condition]
  · simp [transportPullbackIso, iteratedRestrictionIso]

end TransportRestriction

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-- The data of a localized Chern class whose object is represented by a locally bounded complex
of finite locally free modules, as an instance of Situation 0GUJ (alternative (c) of its
condition (3)). -/
abbrev toSituation (hc : ∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ D.E)) :
    LocalizedSituation.{u} where
  toLocalizedChernData := D
  finiteness := Or.inr (Or.inr (Or.inl hc))

end LocalizedChernData

/-- The morphism `X' ×_X X' ⟶ Y' ×_Y Y'` induced by a closed immersion `f : X ⟶ Y` is a closed
immersion: it is a base change of `f`. -/
instance isClosedImmersion_envelopeFibreSquareMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (g : Y' ⟶ Y) : IsClosedImmersion (envelopeFibreSquareMap f g) := by
  rw [← Iso.inv_hom_id_assoc (envelopeFibreSquareFstIso f g) (envelopeFibreSquareMap f g),
    envelopeFibreSquareFstIso_hom_map]
  infer_instance

namespace LocalizedChernData

variable (D : LocalizedChernData.{u}) (H : EnvelopePresentation D.E)

/-- The envelope of a presentation of `E` is proper. -/
instance isProper_envelopePresentation_f : IsProper H.f :=
  H.envelope.isProper

/-- On the source `Y` of an envelope presentation of `E`, the object `Lg^*E` is represented by a
locally bounded complex of finite locally free modules. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_envelope :
    ∃ P : CochainComplex (OXMod.{u, u, u} (D.pullback H.f).X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (D.pullback H.f).E) :=
  ⟨H.P, H.locallyBounded, ⟨H.representation.some.symm⟩⟩

/-- **The situation over an envelope presentation.** For an envelope `g : Y ⟶ X` on which `Lg^*E`
is represented by a locally bounded complex of finite locally free modules, the base change of
the data along `g` is an instance of Situation 0GUJ, through alternative (c) of its
condition (3). -/
abbrev envelopeSituation : LocalizedSituation.{u} :=
  (D.pullback H.f).toSituation (D.exists_isLocallyBoundedFiniteLocallyFree_envelope H)

variable {D}

/-- If `E|_{X ∖ Z}` is zero, so is the restriction of `Lg^*E` away from `Z ×_X Y` on the envelope
`g : Y ⟶ X` of a presentation of `E`. -/
theorem IsZeroOnComplement.envelopeSituation (h : D.IsZeroOnComplement) :
    (D.envelopeSituation H).IsZeroOnComplement :=
  h.pullback

/-- If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, so is the restriction of
`Lg^*E` away from `Z ×_X Y` on the envelope `g : Y ⟶ X` of a presentation of `E`. -/
theorem IsFiniteLocallyFreeOfRankLTOnComplement.envelopeSituation
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    (D.envelopeSituation H).IsFiniteLocallyFreeOfRankLTOnComplement :=
  h.pullback

/-- **The class `P_p(Z ×_X Y ⟶ Y, Lg^*E)` over an envelope presentation `g : Y ⟶ X`**, the class
of Stacks 0FB2 for the situation `Stacks.Chow.LocalizedChernData.envelopeSituation`, read as a
class for the base change `Z ×_X Y ⟶ Y` of `Z ⟶ X`, the group in which Stacks 0GUC descends. -/
def envelopePowerSum (h : D.IsZeroOnComplement) (p : ℕ) :
    BivariantClass D.base (gysinSystemOfInvertible D.base)
      (pullback.fst D.i H.f ≫ (D.i ≫ D.a)) (H.f ≫ D.a) (pullback.snd D.i H.f)
      (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f) p :=
  bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i H.f)
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f) rfl
    (hv := rfl) p ((D.envelopeSituation H).localizedPowerSum h.pullback p)

/-- **The class `c_p(Z ×_X Y ⟶ Y, Lg^*E)` over an envelope presentation `g : Y ⟶ X`**, as
`Stacks.Chow.LocalizedChernData.envelopePowerSum`. -/
def envelopeChern (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    BivariantClass D.base (gysinSystemOfInvertible D.base)
      (pullback.fst D.i H.f ≫ (D.i ≫ D.a)) (H.f ≫ D.a) (pullback.snd D.i H.f)
      (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f) D.p :=
  bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i H.f)
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f) rfl
    (hv := rfl) D.p ((D.envelopeSituation H).localizedChern h.pullback)

/-- The two pullbacks of `Lg^*E` to `Y ×_X Y` along the two projections agree. -/
def derivedPullbackSndIsoFst :
    (derivedPullback (pullback.snd H.f H.f).toLRSHom.toShHom).obj (D.pullback H.f).E ≅
      (derivedPullback (pullback.fst H.f H.f).toLRSHom.toShHom).obj (D.pullback H.f).E :=
  derivedPullbackCompIsoOfScheme (pullback.snd H.f H.f) H.f D.E ≪≫
    eqToIso (congrArg (fun F => F.obj D.E)
      (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
        (congrArg (fun m => m.toLRSHom.toShHom)
          (pullback.condition (f := H.f) (g := H.f)).symm))) ≪≫
    (derivedPullbackCompIsoOfScheme (pullback.fst H.f H.f) H.f D.E).symm

/-- **The descent condition of Stacks 0GUC for `P_p(Z ×_X Y ⟶ Y, Lg^*E)`**: its two restrictions
to `Y ×_X Y` agree. Each is, by Stacks 0FB3 and Stacks 0FB7
(`Stacks.Chow.bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq`), the class of
the graph construction of the pullback of `E` to `Y ×_X Y` for the closed subscheme
`(Z ×_X Y) ×_Z (Z ×_X Y)`; this is the restriction step in Remark 0GUK, which combines Stacks
0FB2, 0FB3 and 0GUC. -/
theorem envelopeDescentRes₁_envelopePowerSum (h : D.IsZeroOnComplement) (p : ℕ) :
    envelopeDescentRes₁ D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (envelopePowerSum H h p) =
      envelopeDescentRes₂ D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (envelopePowerSum H h p) := by
  set SY := D.envelopeSituation H
  set S₂ := SY.pullback (pullback.fst H.f H.f)
  have hY : SY.IsZeroOnComplement := h.pullback
  have h₂ : S₂.IsZeroOnComplement := hY.pullback
  have hR₁ := range_eq_range_pullbackSnd_of_iso (pullback.fst H.f H.f) (pullback.snd D.i H.f)
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareFstIso D.i H.f)
    (envelopeFibreSquareFstIso_hom_map D.i H.f)
  have hT₂ := forall_notMem_of_eq hR₁ S₂.mem_range_graphSubschemeι
  have hrk₂ := forall_notMem_of_eq hR₁ (S₂.finiteLocallyFreeRank_graphSubscheme_eq_zero h₂)
  have e₁ := bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq D.base SY.a
    (pullback.fst H.f H.f) SY.E SY.perfect S₂.E S₂.perfect (Iso.refl _) SY.i
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareFstIso D.i H.f)
    (envelopeFibreSquareFstIso_hom_map D.i H.f) SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a rfl (envelopeFibreSquareMap_comp_structureMorphism D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂ (SY.finiteLocallyFreeRank_graphSubscheme_eq_zero hY)
    hrk₂
  have e₂ := bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq D.base SY.a
    (pullback.snd H.f H.f) SY.E SY.perfect S₂.E S₂.perfect (derivedPullbackSndIsoFst H) SY.i
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareSndIso D.i H.f)
    (envelopeFibreSquareSndIso_hom_map D.i H.f) SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a (by simp [S₂, SY, pullback.condition_assoc])
    (envelopeFibreSquareMap_comp_structureMorphism D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂ (SY.finiteLocallyFreeRank_graphSubscheme_eq_zero hY)
    hrk₂
  refine eq_of_heq ?_
  unfold envelopeDescentRes₁ envelopeDescentRes₂
  refine (heq_of_eq e₁).trans ?_
  refine (bivariantClassCongrBase_heq _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (BivariantClass.congrBase_heq _ _ _).symm
  refine HEq.trans ?_ (heq_of_eq e₂).symm
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

/-- **The descent condition of Stacks 0GUC for `c_p(Z ×_X Y ⟶ Y, Lg^*E)`**, as
`Stacks.Chow.LocalizedChernData.envelopeDescentRes₁_envelopePowerSum`. -/
theorem envelopeDescentRes₁_envelopeChern (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    envelopeDescentRes₁ D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f D.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (envelopeChern H h) =
      envelopeDescentRes₂ D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f D.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (envelopeChern H h) := by
  set SY := D.envelopeSituation H
  set S₂ := SY.pullback (pullback.fst H.f H.f)
  have hY : SY.IsFiniteLocallyFreeOfRankLTOnComplement := h.pullback
  have h₂ : S₂.IsFiniteLocallyFreeOfRankLTOnComplement := hY.pullback
  have hR₁ := range_eq_range_pullbackSnd_of_iso (pullback.fst H.f H.f) (pullback.snd D.i H.f)
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareFstIso D.i H.f)
    (envelopeFibreSquareFstIso_hom_map D.i H.f)
  have hT₂ := forall_notMem_of_eq hR₁ S₂.mem_range_graphSubschemeι
  have hrk₂ := forall_notMem_of_eq hR₁ (S₂.finiteLocallyFreeRank_graphSubscheme_lt h₂)
  have e₁ := bivariantTransport_bivariantRestriction_graphChernClass_of_eq D.base SY.a
    (pullback.fst H.f H.f) SY.E SY.perfect S₂.E S₂.perfect (Iso.refl _) SY.i
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareFstIso D.i H.f)
    (envelopeFibreSquareFstIso_hom_map D.i H.f) SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject D.p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a rfl (envelopeFibreSquareMap_comp_structureMorphism D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂ (SY.finiteLocallyFreeRank_graphSubscheme_lt hY)
    hrk₂
  have e₂ := bivariantTransport_bivariantRestriction_graphChernClass_of_eq D.base SY.a
    (pullback.snd H.f H.f) SY.E SY.perfect S₂.E S₂.perfect (derivedPullbackSndIsoFst H) SY.i
    (envelopeFibreSquareMap D.i H.f) (envelopeFibreSquareSndIso D.i H.f)
    (envelopeFibreSquareSndIso_hom_map D.i H.f) SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject D.p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a (by simp [S₂, SY, pullback.condition_assoc])
    (envelopeFibreSquareMap_comp_structureMorphism D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂ (SY.finiteLocallyFreeRank_graphSubscheme_lt hY)
    hrk₂
  refine eq_of_heq ?_
  unfold envelopeDescentRes₁ envelopeDescentRes₂
  refine (heq_of_eq e₁).trans ?_
  refine (bivariantClassCongrBase_heq _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (BivariantClass.congrBase_heq _ _ _).symm
  refine HEq.trans ?_ (heq_of_eq e₂).symm
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

variable (D)

/-- There is a unique class in `A^p(Z ⟶ X)` restricting to `P_p(Z ×_X Y ⟶ Y, Lg^*E)` along the
envelope `g : Y ⟶ X` of a presentation of `E` (Stacks 0GUC). -/
theorem existsUnique_bivariantRestriction_eq_envelopePowerSum (h : D.IsZeroOnComplement) (p : ℕ) :
    ∃! c : BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl p,
      bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) c =
        envelopePowerSum H h p :=
  existsUnique_bivariantRestriction_eq_of_isEnvelope D.base (D.i ≫ D.a) D.a D.i rfl H.f
    H.envelope p (envelopePowerSum H h p) (envelopeDescentRes₁_envelopePowerSum H h p)

/-- **The localized class `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` when the Chern classes of `E` are
defined** (Remark 0GUK), when `E|_{X ∖ Z}` is zero, for every degree `p`: the unique class whose
restriction along the envelope `g : Y ⟶ X` of a presentation of `E` by a locally bounded complex of
finite locally free modules is the class `P_p(Z ×_X Y ⟶ Y, Lg^*E)` of Stacks 0FB2 (Stacks 0GUC).
In Situation 0GUJ it is the class of Stacks 0FB2
(`Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`). -/
@[stacks 0GUK "P_p(Z → X, E) in A^p(Z → X) for E perfect with E|_{X ∖ Z} zero whose Chern \
classes are defined, by descent (0GUC) of the classes of 0FB2 along an envelope; in Situation \
0GUJ it is the class of 0FB2 (localizedPowerSum_toLocalizedChernData)"]
def localizedPowerSum (hE : HasDefinedChernClasses D.E) (h : D.IsZeroOnComplement) (p : ℕ) :
    BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl p :=
  (D.existsUnique_bivariantRestriction_eq_envelopePowerSum hE.some h p).exists.choose

/-- The restriction of `P_p(Z ⟶ X, E)` along the envelope of the chosen presentation of `E` is
`P_p(Z ×_X Y ⟶ Y, Lg^*E)`. -/
theorem bivariantRestriction_localizedPowerSum (hE : HasDefinedChernClasses D.E)
    (h : D.IsZeroOnComplement) (p : ℕ) :
    bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl
        hE.some.f p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
        (D.localizedPowerSum hE h p) =
      envelopePowerSum hE.some h p :=
  (D.existsUnique_bivariantRestriction_eq_envelopePowerSum hE.some h p).exists.choose_spec

/-- There is a unique class in `A^p(Z ⟶ X)` restricting to `c_p(Z ×_X Y ⟶ Y, Lg^*E)` along the
envelope `g : Y ⟶ X` of a presentation of `E` (Stacks 0GUC). -/
theorem existsUnique_bivariantRestriction_eq_envelopeChern
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    ∃! c : BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl D.p,
      bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f D.p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) c =
        envelopeChern H h :=
  existsUnique_bivariantRestriction_eq_of_isEnvelope D.base (D.i ≫ D.a) D.a D.i rfl H.f
    H.envelope D.p (envelopeChern H h) (envelopeDescentRes₁_envelopeChern H h)

/-- **The localized Chern class `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` when the Chern classes of `E` are
defined** (Remark 0GUK), when `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`: the
unique class whose restriction along the envelope `g : Y ⟶ X` of a presentation of `E` is the class
`c_p(Z ×_X Y ⟶ Y, Lg^*E)` of Stacks 0FB2 (Stacks 0GUC). In Situation 0GUJ it is the class of
Stacks 0FB2 (`Stacks.Chow.LocalizedSituation.localizedChern_toLocalizedChernData`). -/
@[stacks 0GUK "c_p(Z → X, E) in A^p(Z → X) for E perfect with E|_{X ∖ Z} finite locally free \
of rank < p in degree 0 whose Chern classes are defined, by descent (0GUC) of the classes of \
0FB2 along an envelope; in Situation 0GUJ it is the class of 0FB2 \
(localizedChern_toLocalizedChernData)"]
def localizedChern (hE : HasDefinedChernClasses D.E)
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl D.p :=
  (D.existsUnique_bivariantRestriction_eq_envelopeChern hE.some h).exists.choose

/-- **The localized Chern character `ch(Z ⟶ X, E) = ∑_p P_p(Z ⟶ X, E)/p!` when the Chern classes
of `E` are defined** (Definition 0FB5 (1) and Remark 0GUK), when `E|_{X ∖ Z}` is zero, as an
element of `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`. -/
@[stacks 0GUK "the localized Chern character ch(Z → X, E) = Σ_p P_p(Z → X, E)/p! of 0FB5 (1) \
for E perfect with E|_{X ∖ Z} zero whose Chern classes are defined"]
def localizedChernChar (hE : HasDefinedChernClasses D.E) (h : D.IsZeroOnComplement) (p : ℕ) :
    TensorProduct ℤ ℚ
      (BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl (p : ℤ)) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] D.localizedPowerSum hE h p

/-- The restriction of `c_p(Z ⟶ X, E)` along the envelope of the chosen presentation of `E` is
`c_p(Z ×_X Y ⟶ Y, Lg^*E)`. -/
theorem bivariantRestriction_localizedChern (hE : HasDefinedChernClasses D.E)
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl
        hE.some.f D.p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
        (D.localizedChern hE h) =
      envelopeChern hE.some h :=
  (D.existsUnique_bivariantRestriction_eq_envelopeChern hE.some h).exists.choose_spec

variable {D}

/-- The pullbacks of `E` to `Y₀ ×_X Y` through the two presentations agree. -/
def derivedPullbackFstIsoSnd (H₀ H : EnvelopePresentation D.E) :
    (derivedPullback (pullback.fst H₀.f H.f).toLRSHom.toShHom).obj (D.pullback H₀.f).E ≅
      (derivedPullback (pullback.snd H₀.f H.f).toLRSHom.toShHom).obj (D.pullback H.f).E :=
  derivedPullbackCompIsoOfScheme (pullback.fst H₀.f H.f) H₀.f D.E ≪≫
    eqToIso (congrArg (fun F => F.obj D.E)
      (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
        (congrArg (fun m => m.toLRSHom.toShHom)
          (pullback.condition (f := H₀.f) (g := H.f))))) ≪≫
    (derivedPullbackCompIsoOfScheme (pullback.snd H₀.f H.f) H.f D.E).symm

/-- **`P_p(Z ⟶ X, E)` restricts to `P_p(Z ×_X Y ⟶ Y, Lg^*E)` along the envelope `g : Y ⟶ X` of
every presentation of `E`**, not only the chosen one. Let `g₀ : Y₀ ⟶ X` be the envelope of the
chosen presentation and `π₁ : Y₀ ×_X Y ⟶ Y₀`, `π₂ : Y₀ ×_X Y ⟶ Y` the projections; `π₂` is an
envelope, so restriction along it is injective (Stacks 0GUC). Restricting the two sides along
`π₂`: by the compatibility of restriction with composition (Remark 0F9Z) the left side is the
restriction of `P_p(Z ⟶ X, E)` along `g₀ ∘ π₁ = g ∘ π₂`, that is, the restriction along `π₁` of
`P_p(Z ×_X Y₀ ⟶ Y₀, Lg₀^*E)`; by Stacks 0FB3 and Stacks 0FB7 both this and the restriction of
`P_p(Z ×_X Y ⟶ Y, Lg^*E)` along `π₂` are the class of the pullback of `E` to `Y₀ ×_X Y`. -/
theorem bivariantRestriction_localizedPowerSum_envelope (hE : HasDefinedChernClasses D.E)
    (H : EnvelopePresentation D.E) (h : D.IsZeroOnComplement) (p : ℕ) :
    bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
        (D.localizedPowerSum hE h p) =
      envelopePowerSum H h p := by
  have hc₀ := D.bivariantRestriction_localizedPowerSum hE h p
  set H₀ := hE.some
  have hgys : (gysinSystemOfInvertible D.base).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base
  have hπ : IsEnvelope (pullback.snd H₀.f H.f) :=
    isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H₀.f H.f)
      H₀.envelope
  set SY₀ := D.envelopeSituation H₀
  set SY := D.envelopeSituation H
  set S₂ := SY.pullback (pullback.snd H₀.f H.f)
  have hY₀ : SY₀.IsZeroOnComplement := h.pullback
  have hY : SY.IsZeroOnComplement := h.pullback
  have h₂ : S₂.IsZeroOnComplement := hY.pullback
  have hm₁ : pullback.fst H₀.f H.f ≫ H₀.f = pullback.snd H₀.f H.f ≫ H.f := pullback.condition
  have hι₂ : (pullbackLeftPullbackSndIso D.i H.f (pullback.snd H₀.f H.f) ≪≫
      pullback.congrHom rfl rfl).hom ≫ pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) =
        pullback.snd (pullback.snd D.i H.f) (pullback.snd H₀.f H.f) := by simp
  have hι₁ : (pullbackLeftPullbackSndIso D.i H₀.f (pullback.fst H₀.f H.f) ≪≫
      pullback.congrHom rfl hm₁).hom ≫ pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) =
        pullback.snd (pullback.snd D.i H₀.f) (pullback.fst H₀.f H.f) := by simp
  have hR := range_eq_range_pullbackSnd_of_iso (pullback.snd H₀.f H.f) (pullback.snd D.i H.f)
    (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₂
  have hT₂ := forall_notMem_of_eq hR S₂.mem_range_graphSubschemeι
  have hrk₂ := forall_notMem_of_eq hR (S₂.finiteLocallyFreeRank_graphSubscheme_eq_zero h₂)
  have hsB : pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ S₂.a =
      pullback.fst D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ (D.i ≫ D.a) := by
    rw [← pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl, Category.assoc]
  have e₁ := bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq D.base SY₀.a
    (pullback.fst H₀.f H.f) SY₀.E SY₀.perfect S₂.E S₂.perfect (derivedPullbackFstIsoSnd H₀ H)
    SY₀.i (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₁ SY₀.graphSubschemeι
    SY₀.isFiniteLocallyFree_graphObjectRestrictHomology SY₀.hasDefinedChernClasses_graphObject p
    SY₀.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H₀.f)
    S₂.a (by simp [S₂, SY, SY₀, pullback.condition_assoc]) hsB
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂
    (SY₀.finiteLocallyFreeRank_graphSubscheme_eq_zero hY₀) hrk₂
  have e₂ := bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq D.base SY.a
    (pullback.snd H₀.f H.f) SY.E SY.perfect S₂.E S₂.perfect (Iso.refl _)
    SY.i (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₂ SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a rfl hsB
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂
    (SY.finiteLocallyFreeRank_graphSubscheme_eq_zero hY) hrk₂
  have B₁ := bivariantTransport_bivariantRestriction_bivariantRestriction D.base
    (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl p hgys
    (D.localizedPowerSum hE h p) H₀.f (pullback.fst H₀.f H.f) _ hm₁
  have B₂ := bivariantTransport_bivariantRestriction_bivariantRestriction D.base
    (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl p hgys
    (D.localizedPowerSum hE h p) H.f (pullback.snd H₀.f H.f) _ rfl
  rw [hc₀] at B₁
  refine bivariantRestrictionAddHom_injective_of_isEnvelope' D.base _ _ _ _ _
    (pullback.snd H₀.f H.f) p hgys hπ ?_
  refine bivariantTransport_injective D.base _ _
    (pullback.fst D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ (D.i ≫ D.a))
    (pullback.snd H₀.f H.f ≫ (H.f ≫ D.a)) _ _ (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f))
    hsB
    (pullbackLeftPullbackSndIso D.i H.f (pullback.snd H₀.f H.f) ≪≫ pullback.congrHom rfl rfl)
    hι₂ p hgys ?_
  refine eq_of_heq ((heq_of_eq B₂).trans ?_)
  refine (BivariantClass.congrBase_heq _ _ _).trans ?_
  refine (BivariantClass.congrBase_heq _ _ _).symm.trans ((heq_of_eq B₁.symm).trans ?_)
  refine (heq_of_eq e₁).trans ?_
  refine (bivariantClassCongrBase_heq _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (heq_of_eq e₂).symm
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

/-- **`c_p(Z ⟶ X, E)` restricts to `c_p(Z ×_X Y ⟶ Y, Lg^*E)` along the envelope `g : Y ⟶ X` of
every presentation of `E`**, as
`Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedChern_envelope`. -/
theorem bivariantRestriction_localizedChern_envelope (hE : HasDefinedChernClasses D.E)
    (H : EnvelopePresentation D.E) (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl H.f D.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
        (D.localizedChern hE h) =
      envelopeChern H h := by
  have hc₀ := D.bivariantRestriction_localizedChern hE h
  set H₀ := hE.some
  have hgys : (gysinSystemOfInvertible D.base).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base
  have hπ : IsEnvelope (pullback.snd H₀.f H.f) :=
    isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H₀.f H.f)
      H₀.envelope
  set SY₀ := D.envelopeSituation H₀
  set SY := D.envelopeSituation H
  set S₂ := SY.pullback (pullback.snd H₀.f H.f)
  have hY₀ : SY₀.IsFiniteLocallyFreeOfRankLTOnComplement := h.pullback
  have hY : SY.IsFiniteLocallyFreeOfRankLTOnComplement := h.pullback
  have h₂ : S₂.IsFiniteLocallyFreeOfRankLTOnComplement := hY.pullback
  have hm₁ : pullback.fst H₀.f H.f ≫ H₀.f = pullback.snd H₀.f H.f ≫ H.f := pullback.condition
  have hι₂ : (pullbackLeftPullbackSndIso D.i H.f (pullback.snd H₀.f H.f) ≪≫
      pullback.congrHom rfl rfl).hom ≫ pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) =
        pullback.snd (pullback.snd D.i H.f) (pullback.snd H₀.f H.f) := by simp
  have hι₁ : (pullbackLeftPullbackSndIso D.i H₀.f (pullback.fst H₀.f H.f) ≪≫
      pullback.congrHom rfl hm₁).hom ≫ pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) =
        pullback.snd (pullback.snd D.i H₀.f) (pullback.fst H₀.f H.f) := by simp
  have hR := range_eq_range_pullbackSnd_of_iso (pullback.snd H₀.f H.f) (pullback.snd D.i H.f)
    (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₂
  have hT₂ := forall_notMem_of_eq hR S₂.mem_range_graphSubschemeι
  have hrk₂ := forall_notMem_of_eq hR (S₂.finiteLocallyFreeRank_graphSubscheme_lt h₂)
  have hsB : pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ S₂.a =
      pullback.fst D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ (D.i ≫ D.a) := by
    rw [← pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl, Category.assoc]
  have e₁ := bivariantTransport_bivariantRestriction_graphChernClass_of_eq D.base SY₀.a
    (pullback.fst H₀.f H.f) SY₀.E SY₀.perfect S₂.E S₂.perfect (derivedPullbackFstIsoSnd H₀ H)
    SY₀.i (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₁ SY₀.graphSubschemeι
    SY₀.isFiniteLocallyFree_graphObjectRestrictHomology SY₀.hasDefinedChernClasses_graphObject D.p
    SY₀.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H₀.f)
    S₂.a (by simp [S₂, SY, SY₀, pullback.condition_assoc]) hsB
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂
    (SY₀.finiteLocallyFreeRank_graphSubscheme_lt hY₀) hrk₂
  have e₂ := bivariantTransport_bivariantRestriction_graphChernClass_of_eq D.base SY.a
    (pullback.snd H₀.f H.f) SY.E SY.perfect S₂.E S₂.perfect (Iso.refl _)
    SY.i (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f)) _ hι₂ SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject D.p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    S₂.a rfl hsB
    S₂.graphSubschemeι S₂.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.hasDefinedChernClasses_graphObject hT₂
    (SY.finiteLocallyFreeRank_graphSubscheme_lt hY) hrk₂
  have B₁ := bivariantTransport_bivariantRestriction_bivariantRestriction D.base
    (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl D.p hgys
    (D.localizedChern hE h) H₀.f (pullback.fst H₀.f H.f) _ hm₁
  have B₂ := bivariantTransport_bivariantRestriction_bivariantRestriction D.base
    (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl D.p hgys
    (D.localizedChern hE h) H.f (pullback.snd H₀.f H.f) _ rfl
  rw [hc₀] at B₁
  refine bivariantRestrictionAddHom_injective_of_isEnvelope' D.base _ _ _ _ _
    (pullback.snd H₀.f H.f) D.p hgys hπ ?_
  refine bivariantTransport_injective D.base _ _
    (pullback.fst D.i (pullback.snd H₀.f H.f ≫ H.f) ≫ (D.i ≫ D.a))
    (pullback.snd H₀.f H.f ≫ (H.f ≫ D.a)) _ _ (pullback.snd D.i (pullback.snd H₀.f H.f ≫ H.f))
    hsB
    (pullbackLeftPullbackSndIso D.i H.f (pullback.snd H₀.f H.f) ≪≫ pullback.congrHom rfl rfl)
    hι₂ D.p hgys ?_
  refine eq_of_heq ((heq_of_eq B₂).trans ?_)
  refine (BivariantClass.congrBase_heq _ _ _).trans ?_
  refine (BivariantClass.congrBase_heq _ _ _).symm.trans ((heq_of_eq B₁.symm).trans ?_)
  refine (heq_of_eq e₁).trans ?_
  refine (bivariantClassCongrBase_heq _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (heq_of_eq e₂).symm
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

/-- The presentation of `E` by an envelope `g : Y ⟶ X` on which `Lg^*E` is represented by a locally
bounded complex of finite locally free modules. -/
def envelopePresentationOfIsEnvelope {Y : Scheme.{u}} (g : Y ⟶ D.X) (hg : IsEnvelope g)
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj D.E)) :
    EnvelopePresentation D.E where
  Y := Y
  f := g
  envelope := hg
  P := hc.choose
  locallyBounded := hc.choose_spec.1
  representation := ⟨hc.choose_spec.2.some.symm⟩

/-- **`P_p(Z ⟶ X, E)` restricts along an envelope to the class of Stacks 0FB2 upstairs.** For an
envelope `g : Y ⟶ X` on which `Lg^*E` is represented by a locally bounded complex of finite
locally free modules, the restriction of `P_p(Z ⟶ X, E)` along `g`, read with the source over the
base through `Y`, is the class `P_p(Z ×_X Y ⟶ Y, Lg^*E)` of Stacks 0FB2 for the situation
`(Y, Z ×_X Y, Lg^*E)`, an instance of Situation 0GUJ through alternative (c) of its
condition (3). -/
theorem bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
    (hE : HasDefinedChernClasses D.E) {Y : Scheme.{u}} (g : Y ⟶ D.X) [LocallyOfFiniteType g]
    (hg : IsEnvelope g)
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} (D.pullback g).X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ (D.pullback g).E))
    (h : D.IsZeroOnComplement) (p : ℕ) :
    bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i g)
        (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g)
        (hv' := rfl) p
        (bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
          (D.localizedPowerSum hE h p)) =
      ((D.pullback g).toSituation hc).localizedPowerSum h.pullback p := by
  have key := bivariantRestriction_localizedPowerSum_envelope hE
    (D.envelopePresentationOfIsEnvelope g hg hc) h p
  refine eq_of_heq ((bivariantClassCongrBase_heq _ _ _ _ _).trans ?_)
  refine (heq_of_eq key).trans ?_
  exact bivariantClassCongrBase_heq _ _ _ _ _

/-- **`c_p(Z ⟶ X, E)` restricts along an envelope to the class of Stacks 0FB2 upstairs**, as
`Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum`. -/
theorem bivariantClassCongrBase_bivariantRestriction_localizedChern
    (hE : HasDefinedChernClasses D.E) {Y : Scheme.{u}} (g : Y ⟶ D.X) [LocallyOfFiniteType g]
    (hg : IsEnvelope g)
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} (D.pullback g).X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ (D.pullback g).E))
    (h : D.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i g)
        (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g)
        (hv' := rfl) D.p
        (bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl g
          D.p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
          (D.localizedChern hE h)) =
      ((D.pullback g).toSituation hc).localizedChern h.pullback := by
  have key := bivariantRestriction_localizedChern_envelope hE
    (D.envelopePresentationOfIsEnvelope g hg hc) h
  refine eq_of_heq ((bivariantClassCongrBase_heq _ _ _ _ _).trans ?_)
  refine (heq_of_eq key).trans ?_
  exact bivariantClassCongrBase_heq _ _ _ _ _

end LocalizedChernData

namespace LocalizedSituation

variable (S : LocalizedSituation.{u})

/-- In Situation 0GUJ the restriction of `P_p(Z ⟶ X, E)` along the envelope of any presentation
of `E` is `P_p(Z ×_X Y ⟶ Y, Lg^*E)`: Stacks 0FB3. -/
theorem bivariantRestriction_localizedPowerSum_envelope (H : EnvelopePresentation S.E)
    (h : S.IsZeroOnComplement) (p : ℕ) :
    bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl H.f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) (S.localizedPowerSum h p) =
      LocalizedChernData.envelopePowerSum (D := S.toLocalizedChernData) H h p := by
  have key := LocalizedSituation.bivariantRestriction_localizedPowerSum (S := S) H.f h p
  refine eq_of_heq ((bivariantClassCongrBase_heq (pullback.snd S.i H.f) _ rfl _
    (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl H.f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (S.localizedPowerSum h p))).symm.trans ((heq_of_eq key).trans ?_))
  unfold LocalizedChernData.envelopePowerSum
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

/-- **In Situation 0GUJ the class of Remark 0GUK is the class `P_p(Z ⟶ X, E)` of Stacks 0FB2**:
both restrict to `P_p(Z ×_X Y ⟶ Y, Lg^*E)` along an envelope (Stacks 0FB3), and the uniqueness
in Stacks 0GUC applies. -/
@[stacks 0GUK "the extension agrees with the definition: in Situation 0GUJ the class P_p(Z → X, \
E) of the remark is the class of 0FB2"]
theorem localizedPowerSum_toLocalizedChernData (h : S.IsZeroOnComplement) (p : ℕ) :
    S.toLocalizedChernData.localizedPowerSum S.hasDefinedChernClasses_E h p =
      S.localizedPowerSum h p :=
  (S.toLocalizedChernData.existsUnique_bivariantRestriction_eq_envelopePowerSum
    S.hasDefinedChernClasses_E.some h p).unique
    (S.toLocalizedChernData.bivariantRestriction_localizedPowerSum S.hasDefinedChernClasses_E h p)
    (S.bivariantRestriction_localizedPowerSum_envelope _ h p)

/-- In Situation 0GUJ the restriction of `c_p(Z ⟶ X, E)` along the envelope of any presentation
of `E` is `c_p(Z ×_X Y ⟶ Y, Lg^*E)`: Stacks 0FB3. -/
theorem bivariantRestriction_localizedChern_envelope (H : EnvelopePresentation S.E)
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl H.f S.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base) (S.localizedChern h) =
      LocalizedChernData.envelopeChern (D := S.toLocalizedChernData) H h := by
  have key := LocalizedSituation.bivariantRestriction_localizedChern (S := S) H.f h
  refine eq_of_heq ((bivariantClassCongrBase_heq (pullback.snd S.i H.f) _ rfl _
    (bivariantRestriction S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl H.f S.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        (S.localizedChern h))).symm.trans ((heq_of_eq key).trans ?_))
  unfold LocalizedChernData.envelopeChern
  exact (bivariantClassCongrBase_heq _ _ _ _ _).symm

/-- **In Situation 0GUJ the class of Remark 0GUK is the class `c_p(Z ⟶ X, E)` of Stacks 0FB2**,
as `Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`. -/
@[stacks 0GUK "the extension agrees with the definition: in Situation 0GUJ the class c_p(Z → X, \
E) of the remark is the class of 0FB2"]
theorem localizedChern_toLocalizedChernData (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    S.toLocalizedChernData.localizedChern S.hasDefinedChernClasses_E h =
      S.localizedChern h :=
  (S.toLocalizedChernData.existsUnique_bivariantRestriction_eq_envelopeChern
    S.hasDefinedChernClasses_E.some h).unique
    (S.toLocalizedChernData.bivariantRestriction_localizedChern S.hasDefinedChernClasses_E h)
    (S.bivariantRestriction_localizedChern_envelope _ h)

/-- In Situation 0GUJ the localized Chern character of Remark 0GUK is that of Definition 0FB5. -/
theorem localizedChernChar_toLocalizedChernData (h : S.IsZeroOnComplement) (p : ℕ) :
    S.toLocalizedChernData.localizedChernChar S.hasDefinedChernClasses_E h p =
      S.localizedChernChar h p := by
  rw [LocalizedChernData.localizedChernChar, localizedPowerSum_toLocalizedChernData]

end LocalizedSituation

end Stacks.Chow
