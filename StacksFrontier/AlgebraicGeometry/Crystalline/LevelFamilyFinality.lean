module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAffineFinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFamilyIdentification
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal

/-!
# `hdet` discharged: the faithfulness half of [Stacks, Tag 07JH]

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAffineFinality.lean` leaves the faithfulness half
of [Stacks, Proposition 60.17.4, Tag 07JH] standing on three hypotheses: `hlev`, the weak finality
of the levels on the chaotic subsite `𝒞`, carried as a level `level C` and a morphism
`(wholeι S).obj C ⟶ T_{level C}` for every divided power thickening `C` of the whole of `X`; and
`hlqc`, `hsurj`, which are hypotheses (1) and (2) of [Stacks, Proposition 60.20.1, Tag 07JN].

**This module proves `hlev`, and with it `hdet`, and it discharges `hlqc` and `hsurj`.**  The
faithfulness half costs nothing afterwards beyond the delimiter `hL`: `hsurj` is hypothesis (2) of
[Stacks, Tag 07JN], which follows from the crystal property of the coefficient object by
`...SmallSite.isSurjectiveComparison_of_isSheafCrystal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalComparisonSurjectivity.lean`.

## The two level families, identified in degree zero

The obstruction that note records is that the levels [Stacks, Lemma 60.5.6, Tag 07HP] produces
morphisms out of and the levels the hypothesis is stated over are built in opposite orders:
`Crystalline.levelCrystallineThickening` is the envelope of the truncation `P/(p)^e`, while the
levels of `...SmallSite.wholeSpaceSystem` are the truncations `D̂/(p)^{N + e}` of the completed
envelope.  `Crystalline.levelFamilyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyIdentification.lean` identifies them, for
an object of `Cris^∧(C/A)` pinned down by three hypotheses, and
`Crystalline.exists_levelThickening_hom` draws [Stacks, Tag 07HP] for the second family — but at
the object `Crystalline.completedCrystallineThickening s f hf`, the completed envelope of the
presentation `f` itself, and at a single level.

That is the wrong object, and it is why the note records the two families as envelopes of
**different presentation algebras even in degree zero**: `...SmallSite.wholeSpaceSystem` is built
from `Crystalline.tensorPowerEnvelopeThickening s f hf 0`, the completed envelope of
`Crystalline.tensorPowerPresentation s f 0`, which presents `s.C` from
`MvPolynomial (Fin 1 × ι) s.A` and not from `MvPolynomial ι s.A`.

**No comparison of the two presentations is needed.**  `Crystalline.levelFamilyIso` is stated for
an arbitrary presentation `f : P →ₐ[s.A] s.C` and an arbitrary object of `Cris^∧(C/A)` subject to
its three pinning hypotheses, so it may be applied at
`Crystalline.tensorPowerPresentation s f 0` directly; and the three pinning hypotheses are then
three fields of `Crystalline.CompletedEnvelopeThickening` on the nose, after the two `rfl`s
`Crystalline.completedEnvelopeDPRing_eq` and
`Crystalline.presentationEnvelope_eq_polynomialDividedPowerEnvelope` that
`LevelFamilyIdentification.lean` records.  `Crystalline.envelopeCodiagonal`, the morphism of
uncompleted envelopes that note names as the only existing comparison of the two presentations, is
not used.

The index offset the note also names — `uniformLevel s + e` against a bare `e` — costs nothing
once the statement is in the `∀ e, N ≤ e` form rather than the `∃ e` form, which
`Crystalline.exists_forall_le_levelEnvelope_hom` supplies on the first family and
`Crystalline.exists_forall_le_levelThickening_hom` below carries to the second: a level past both
`N` and `Crystalline.uniformLevel s` can be *written* as `uniformLevel s + e`, and
`Crystalline.IsPAdicLevel` being a `Prop`, the level hypothesis it comes with is the one
`Crystalline.isPAdicLevel_uniformLevel_add` provides.

## Main results

`exists_forall_le_levelThickening_hom` is in the namespace `Crystalline`, the rest in
`Crystalline.GlobalCrystallineSituation.SmallSite`.

* `Crystalline.exists_forall_le_levelThickening_hom` — **[Stacks, Tag 07HP] for the finite levels
  of the completed envelope of any polynomial presentation, at every sufficiently large level.**
* `exists_hom_to_wholeSpaceSystem_level` — **`hlev`: every divided power thickening of the whole
  of `X` admits a morphism to a finite level of the system `(X, T(n)_e, δ(n))` of
  [Stacks, Tag 07JN] in degree zero.**
* `det_of_wholeSpaceSystem` — **`hdet`: a morphism of crystals in quasi-coherent
  `𝒪_{X/S}`-modules is determined by its restrictions to the levels.**  No hypothesis beyond the
  delimiter `hL`.
* `LevelComparison07JG.faithful_functor_of_wholeSpaceSystem` and
  `LevelReduction07JG.faithful_functor07JG_of_wholeSpaceSystem` — **the faithfulness half of
  [Stacks, Tag 07JH]**, with no hypothesis beyond the delimiter `hL`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Two separate things stand in the way, and they should not be confused with one another.

* The **full and essentially-surjective halves** are untouched.  `Functor.Full`,
  `Functor.EssSurj` and `Functor.IsEquivalence` are not mentioned below.  They are the
  construction of the quasi-inverse — the Taylor comparison `c_{f,g}` in all divided power
  degrees, its finiteness from item (07JE), and the cocycle identity
  `c_{g,h} ∘ c_{f,g} = c_{f,h}` — whose state is recorded in
  `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairsEquivalence.lean`, which carries the
  first-order part and no more.
* The **faithfulness half** is proved, with no hypothesis the source does not make.  It is still
  only one of the three halves, which is why the statements below carry no attribute even though
  the half they prove is a half of the tag.  See the next section for how its last hypothesis is
  discharged.

`hdet` is **not a hypothesis**: `det_of_wholeSpaceSystem` proves it outright, from the weak
finality of the levels `exists_hom_to_wholeSpaceSystem_level`, which is [Stacks, Tag 07HP] read
across `...GlobalCrystallineSituation.wholeSiteEquivLittleAffine`.  Nothing below stands in for a
missing result about the site, about the comparison datum, about the connection, or about the four
items of [Stacks, Tag 07JG].

`hlqc`, hypothesis (1) of [Stacks, Tag 07JN], is **discharged**: a crystal in quasi-coherent
modules is quasi-coherent by definition, and the half of [Stacks, Lemma 60.14.2, Tag 07IT] the
library proves holds on the small site, as
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/QuasicoherentImpliesLocal.lean`.  That
module is imported here and in none of `LevelFaithfulSurjectivity.lean`,
`LevelCrystalDeterminacy.lean`, `LevelAmbientDeterminacy.lean` or `LevelAffineFinality.lean`,
which is the only reason those four thread `hlqc` through.

`hL`, that the system of levels is the degree-zero member of `...SmallSite.wholeSpaceSystem`, is a
**delimiter and not a weakening**: it is what `...SmallSite.LevelReduction07JG.toReduction07JG`
already takes in order to produce the field
`...SmallSite.Reduction07JG.levelSystem_isLevel`, which is the hypothesis bundle the tag is stated
against; and it is the system `T_e = Spec(D_e)` the source's own proof fixes, "as in the proof of
Lemma 60.17.3".  It is refuted by the degenerate system over the empty open of `X`
(`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`), so it is not vacuous.

## How the last hypothesis of the faithfulness half is discharged

The last hypothesis is `hsurj`, hypothesis (2) of [Stacks, Proposition 60.20.1, Tag 07JN]:
`...SmallSite.CohomologyRestriction.IsSurjectiveComparison F.obj.val`, that the comparison map
`c_f : f^* ℱ_{T'} ⟶ ℱ_T` of *presheaves* of modules is locally surjective for every closed
immersion.  It enters through `...SmallSite.surjective_levelSystem_module_map_of_eq`, which is
where the surjectivity of the one-step level restrictions `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` comes
from, and that surjectivity is what makes every section over a level the component of an element
of `M = lim_e Γ(T_e, ℱ)`.

It is a theorem on the source's own hypotheses, which is where the source gets it: the proof
of [Stacks, Tag 07JH] does not invoke [Stacks, Tag 07JN] at all, and the corresponding fact is
got, in the proof of [Stacks, Tag 07JG], from the crystal property — "since `ℱ` is a crystal we
have `M_e = M_{e + 1}/p^e M_{e + 1}`".  The statement is
`...SmallSite.isSurjectiveComparison_of_isSheafCrystal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalComparisonSurjectivity.lean`, applied
to the crystal clause `F.property.2` of an object of `...SmallSite.QuasiCoherentCrystal`.  Nothing
about quasi-coherence is needed.

An apparent obstruction does not apply.  The crystal property in
the library is `...SmallSite.IsSheafCrystal`, which asserts that
`...CohomologyRestriction.moduleComparisonSheaf` — the comparison map of *sheaves* of modules,
whose source is the **sheafification** of the source of the presheaf comparison map
`...CohomologyRestriction.moduleComparison` — is an isomorphism; and the two *isomorphism*
conditions are genuinely inequivalent, the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsModules/SheafCrystal.lean` exhibiting a
countable disjoint union of `Spec 𝔽_p` on which the sheaf-level condition is strictly weaker.  But
`IsSurjectiveComparison` does not ask for an isomorphism: it asks for *local* surjectivity, which
is invariant under sheafification.  The presheaf-level comparison morphism factors as the locally
bijective sheafification unit followed by the sheaf-level comparison map, so the sheaf-level
isomorphism already gives presheaf-level local surjectivity.  In the counterexample the
presheaf-level comparison morphism is indeed locally surjective while failing to be an isomorphism.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.14.2, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

noncomputable section

namespace Crystalline

/-! ### [Stacks, Tag 07HP] for the finite levels of a completed envelope -/

variable {s : AffineCrystallineSituation.{u, u}} {ι : Type u}
  (q : MvPolynomial ι s.A →ₐ[s.A] s.C) (hq : Function.Surjective q)

/-- **[Stacks, Lemma 60.5.6, Tag 07HP] for the finite levels of the completed divided power
envelope of a polynomial presentation, at every sufficiently large level**: every divided power
thickening `B` of `C/A` receives a morphism from `D̂/(p)^e` for all large `e`.

`Crystalline.exists_levelThickening_hom` is the same statement at the single object
`Crystalline.completedCrystallineThickening s q hq` and for a single level.  Both generalisations
are needed to reach the levels of `...SmallSite.wholeSpaceSystem`, which are the levels of
`Crystalline.tensorPowerEnvelopeThickening` and not of
`Crystalline.completedCrystallineThickening`: the object is arbitrary subject to being a
realisation of the completed envelope of some polynomial presentation, which is what lets the
*other* presentation `Crystalline.tensorPowerPresentation s q 0` be used, and the level is
arbitrary subject to being large, which is what lets it be written in the form
`Crystalline.uniformLevel s + e` the system is indexed by.

The three hypotheses `Crystalline.levelFamilyIso` pins its object down with are three fields of
`Crystalline.CompletedEnvelopeThickening`, read across the two `rfl`s
`Crystalline.completedEnvelopeDPRing_eq` and
`Crystalline.presentationEnvelope_eq_polynomialDividedPowerEnvelope`; so nothing is carried beyond
surjectivity of the presentation. -/
@[stacks 07HP "for every sufficiently large finite level of the completed envelope"]
theorem exists_forall_le_levelThickening_hom (W : CompletedEnvelopeThickening s q hq)
    (B : DividedPowerThickening.{u, u, u} s) :
    ∃ N : ℕ, ∀ e, N ≤ e →
      ∃ h : IsPAdicLevel W.thickening.ring.ideal W.thickening.ring.dividedPowers s.p e,
        Nonempty (levelThickeningObj W.thickening e h ⟶ B) := by
  classical
  obtain ⟨N₁, h₁⟩ := levelFamilyIso q hq W.thickening W.hp
    (W.ring_eq.trans (completedEnvelopeDPRing_eq s q hq W.hp)) W.fromBase_eq W.quotient_compat
  obtain ⟨N₂, h₂⟩ := exists_forall_le_levelEnvelope_hom s ⟨ι, ⟨AlgEquiv.refl⟩⟩ q hq B
  refine ⟨max N₁ N₂, fun e he => ?_⟩
  obtain ⟨h, _, iso⟩ := h₁ e ((le_max_left _ _).trans he)
  obtain ⟨_, ⟨φ⟩⟩ := h₂ e ((le_max_right _ _).trans he)
  exact ⟨h, ⟨iso.hom ≫ φ⟩⟩

namespace GlobalCrystallineSituation.SmallSite

/-! ### `hlev`: every thickening of the whole space maps to a level -/

variable {T : GlobalCrystallineSituation.{u}} [IsAffine T.X] [IsAffine T.S.scheme]
  (hp : IsNilpotent (T.p : Γ(T.X, ⊤)))

/-- **`hlev`, the weak finality of the levels on the chaotic subsite `𝒞`**: every divided power
thickening of the whole of `X` admits a morphism to a finite level of the system
`(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] in degree zero.

This is the hypothesis `...SmallSite.det_of_wholeSpaceLevelSections` carries, and it is
[Stacks, Lemma 60.5.6, Tag 07HP] read across the equivalence
`...GlobalCrystallineSituation.wholeSiteEquivLittleAffine : 𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`.  Only
the ring side was outstanding, and it is
`Crystalline.exists_forall_le_levelThickening_hom` at the object
`Crystalline.tensorPowerEnvelopeThickening` in degree zero that `...SmallSite.wholeSpaceSystem` is
built from.  The direction is the one wanted: a morphism out of a level in
`Cris(Γ(X, ⊤)/Γ(S, ⊤))` is a morphism into that level in `𝒞`, and the passage is the unit of the
equivalence.

Weak finality of a *fixed* level would be false — an object on which `p^m` does not vanish admits
no morphism to `T_e` with `N + e < m` — and is not asserted: the level varies with the thickening,
exactly as in [Stacks, Tag 07HP]. -/
theorem exists_hom_to_wholeSpaceSystem_level [WholeSpacePresentation T hp]
    (C : WholeSpaceThickening T) :
    ∃ e : ℕ, Nonempty ((wholeι T).obj C ⟶
      ((wholeSpaceSystem T hp).obj (op (SimplexCategory.mk 0))).obj e) := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_le_levelThickening_hom
    (tensorPowerPresentation (affineSituation T hp) (wholeSpacePresentation T hp) 0)
    (tensorPowerPresentation_surjective _ _ (wholeSpacePresentation_surjective T hp) 0)
    (tensorPowerEnvelopeThickening (affineSituation T hp) (wholeSpacePresentation T hp)
      (wholeSpacePresentation_surjective T hp) 0)
    ((wholeSiteEquivLittleAffine hp).functor.obj (op C)).obj
  refine ⟨max N (uniformLevel (affineSituation T hp)) -
    uniformLevel (affineSituation T hp), ?_⟩
  obtain ⟨h, ⟨φ⟩⟩ := hN (uniformLevel (affineSituation T hp) +
    (max N (uniformLevel (affineSituation T hp)) -
      uniformLevel (affineSituation T hp))) (by omega)
  exact ⟨(wholeι T).map
    (((wholeSiteEquivLittleAffine hp).inverse.map (ObjectProperty.homMk φ) ≫
      (wholeSiteEquivLittleAffine hp).unitInv.app (op C))).unop⟩

/-- A crystal in quasi-coherent modules is locally quasi-coherent. -/
private theorem isLocallyQuasiCoherent_quasiCoherentCrystal {T : GlobalCrystallineSituation.{u}}
    (F : QuasiCoherentCrystal T) : IsLocallyQuasiCoherent F.obj :=
  isLocallyQuasiCoherent_of_isQuasicoherentOnSite F.obj F.property.1

/-- The comparison map of a crystal in quasi-coherent modules is locally surjective. -/
private theorem isSurjectiveComparison_quasiCoherentCrystal {T : GlobalCrystallineSituation.{u}}
    (F : QuasiCoherentCrystal T) : CohomologyRestriction.IsSurjectiveComparison F.obj.val :=
  isSurjectiveComparison_of_isSheafCrystal F.property.2

/-! ### `hdet` and the faithfulness half of [Stacks, Tag 07JH] -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG T D}

/-- **`hdet`: two morphisms of crystals in quasi-coherent `𝒪_{X/S}`-modules which agree on
`Γ(T_e, ℱ)` for every level are equal.**

This is `...SmallSite.det_of_wholeSpaceLevelSections` with both of its outstanding hypotheses
gone: `hlev` by `exists_hom_to_wholeSpaceSystem_level`, and `hlqc` by
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` applied to the quasi-coherence a
crystal in quasi-coherent modules carries by definition.  So nothing is left but the delimiter
`hL`.

`hdet` is the hypothesis of `...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel`, and it
is the geometric content of the faithfulness half of [Stacks, Tag 07JH]: the source's proof gets
it from the weak finality of the levels, [Stacks, Lemma 60.5.6, Tag 07HP], and so does this. -/
theorem det_of_wholeSpaceSystem [WholeSpacePresentation T hp]
    (hL : L.levelSystem = (wholeSpaceSystem T hp).obj (op (SimplexCategory.mk 0)))
    {F G : QuasiCoherentCrystal T} (psi chi : F ⟶ G)
    (hs : ∀ (e : ℕ) (x : F.obj.val.obj (op (L.levelSystem.obj e))),
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι T).map psi).val
          (op (L.levelSystem.obj e))).hom x =
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι T).map chi).val
          (op (L.levelSystem.obj e))).hom x) :
    psi = chi := by
  classical
  have key : ∀ C : WholeSpaceThickening T,
      ∃ e : ℕ, Nonempty ((wholeι T).obj C ⟶ L.levelSystem.obj e) := by
    intro C
    rw [hL]
    exact exists_hom_to_wholeSpaceSystem_level hp C
  exact det_of_wholeSpaceLevelSections hp hL
    isLocallyQuasiCoherent_quasiCoherentCrystal
    (fun C => (key C).choose) (fun C => (key C).choose_spec.some) psi chi hs

/-- **The faithfulness half of [Stacks, Proposition 60.17.4, Tag 07JH] for the constructed
functor**, with no hypothesis beyond the delimiter `hL`.

`...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` runs on `hdet`, `hlqc` and `hsurj`.
`det_of_wholeSpaceSystem` proves `hdet`,
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` discharges `hlqc`, and `hsurj` —
hypothesis (2) of [Stacks, Proposition 60.20.1, Tag 07JN] — is
`...SmallSite.isSurjectiveComparison_of_isSheafCrystal` at the crystal clause of the coefficient
object, which is how the source gets it too.

**This is not [Stacks, Tag 07JH] and no tag attribute is placed**: the full and
essentially-surjective halves are untouched, and a tag belongs on the covering set of its own
assertion, not on one of its three halves. -/
theorem LevelComparison07JG.faithful_functor_of_wholeSpaceSystem
    (C : LevelComparison07JG T A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem T hp).obj (op (SimplexCategory.mk 0))) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_isLevel hp hL
    isLocallyQuasiCoherent_quasiCoherentCrystal
    isSurjectiveComparison_quasiCoherentCrystal
    fun psi chi hs => det_of_wholeSpaceSystem hp hL psi chi hs

/-- **The functor of [Stacks, Lemma 60.17.3, Tag 07JG] is faithful**, with no hypothesis beyond
the delimiter `hL`; this is the first of the three halves of
[Stacks, Proposition 60.17.4, Tag 07JH].

The passage from the constructed functor to the tag's own functor costs nothing, by
`...SmallSite.faithful_functor07JG_iff`, `Crystalline.firstOrderCrystalsToPairs` being
unconditionally faithful.

**This is not [Stacks, Tag 07JH] and no tag attribute is placed**: it is the faithfulness half, for
the functor of a level reduction datum.  [Stacks, Tag 07JH] itself is
`...SmallSite.crystalPairFunctor_isEquivalence`, for the functor `...SmallSite.crystalPairFunctor`.
Hypothesis (2) of [Stacks, Tag 07JN] is not assumed: it follows from the crystal property, by
`...SmallSite.isSurjectiveComparison_of_isSheafCrystal`. -/
theorem LevelReduction07JG.faithful_functor07JG_of_wholeSpaceSystem
    (R : LevelReduction07JG T A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem T hp).obj (op (SimplexCategory.mk 0))) :
    Functor.Faithful (functor07JG (R.toReduction07JG (hp := hp) hL)) :=
  R.faithful_functor07JG_of_isLevel hp hL
    isLocallyQuasiCoherent_quasiCoherentCrystal
    isSurjectiveComparison_quasiCoherentCrystal
    fun psi chi hs => det_of_wholeSpaceSystem hp hL psi chi hs

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
