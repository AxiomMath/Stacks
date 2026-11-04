module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelReductionFaithful
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity

/-!
# The surjectivity hypothesis of the faithfulness half of [Stacks, Tag 07JH], discharged

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelReductionFaithful.lean` factors the faithfulness
half of [Stacks, Proposition 60.17.4, Tag 07JH] into two hypotheses:
`...SmallSite.LevelComparison07JG.faithful_functor_of_surjective_step` takes `hdet`, that a
morphism of crystals is determined by its restrictions to the levels, and `hstep`, surjectivity
of each one-step restriction `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` of the system of levels.  Its module
documentation records `hstep` as not identified with anything the tree proves, the obstruction
being that
`...SmallSite.surjective_affineSections_finiteLevelSystem_transition` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelRestrictionSurjectivity.lean` is stated
for `Crystalline.finiteLevelSections` of the little affine crystalline category rather than for
the levels of `...SmallSite.wholeSpaceSystem`.

**This module discharges `hstep`.**  The identification across
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` that the note asks for is not
needed: the same file already carries the whole-space spelling of the surjectivity, in
`...SmallSite.surjective_wholeSpaceSystem_level_map`, and the piece that was genuinely missing is
the *module-valued* reading of it — the level restriction of a sheaf of `𝒪_{X/S}`-modules rather
than of its underlying abelian sheaf at the coefficient universe `u + 1`, which is the map
`hstep` is about.  That reading is
`...CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` of the same file, instantiated at
the level drops of the system; the transport across the equivalence sits inside
`...SmallSite.isClosedImmersion_targetHom_inverse_map`, which that instantiation calls.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `surjective_wholeSpaceSystem_module_level_map` — **the level restriction
  `Γ((X, T(n)_{e + 1}, δ(n)), ℱ) ⟶ Γ((X, T(n)_e, δ(n)), ℱ)` of a sheaf of `𝒪_{X/S}`-modules is
  surjective**, under hypotheses (1) and (2) of [Stacks, Tag 07JN] and nothing else.  This is
  `...SmallSite.surjective_wholeSpaceSystem_level_map` read on the presheaf of modules instead of
  on the underlying abelian sheaf.
* `surjective_levelSystem_module_map_of_eq` — the same for a system of levels that *is* the
  degree-zero member of `...SmallSite.wholeSpaceSystem`, which is the hypothesis
  `...SmallSite.Reduction07JG.levelSystem_isLevel` names.  This is `hstep` of
  `...SmallSite.LevelComparison07JG.faithful_functor_of_surjective_step`.
* `LevelComparison07JG.faithful_functor_of_isLevel` — **the faithfulness half of
  [Stacks, Tag 07JH] for the constructed functor, from `hdet` alone** together with hypotheses
  (1) and (2) of [Stacks, Tag 07JN] for the crystals.
* `LevelReduction07JG.faithful_functor07JG_of_isLevel` — the same conclusion for the tag's own
  functor.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed
in this module.**  The full and
essentially-surjective halves are untouched, and `Functor.IsEquivalence` is not mentioned below.
What changes against `LevelReductionFaithful.lean` is which hypotheses the faithfulness half
carries.

* `hstep` is **gone**: it is proved, for the system of levels of [Stacks, Tag 07JN], from
  hypotheses (1) and (2) of that proposition.  Nothing stands in for it.
* `hdet` is **unchanged and still a stand-in**: that a morphism of crystals in quasi-coherent
  `𝒪_{X/S}`-modules is determined by its restrictions to the levels.  It is the geometric content
  of this half of the tag and nothing in the tree proves it.  See the section below for what it
  rests on, which is not what `LevelReductionFaithful.lean` recorded.

## What `hdet` rests on

The source's proof of [Stacks, Tag 07JH] gets the determinacy from weak finality of the levels,
invoking [Stacks, Lemma 60.5.6, Tag 07HP]: every object of `CRIS(C/A)` receives a morphism from a
sufficiently high finite level of the divided power envelope.  **That lemma is formalized**, as
`Crystalline.exists_levelEnvelope_hom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean`, carrying `@[stacks 07HP]`,
with the level depending on the object through the nilpotency exponent of `p` on it.  Its
direction is the one wanted: `...GlobalCrystallineSituation.wholeSiteEquivLittleAffine` is an
equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`, so a morphism *out of* a level there is a morphism
*into* that level in `𝒞 ⊆ Cris(X/S)`.  Passing from an arbitrary affine object of `Cris(X/S)` to
an object of `𝒞` is `...SmallSite.exists_hom_to_wholeSpaceThickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalNonempty.lean`.

What is false, and is the statement the note of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean` refutes, is weak
finality of a **fixed** level: an object on which `p^m` does not vanish admits no morphism to
`T_e` with `N + e < m`.  The existential form is not refuted by that argument and is what
[Stacks, Tag 07HP] supplies.

Two things still stand between [Stacks, Tag 07HP] and `hdet`, and they are what a proof of it
would have to supply.

1. The levels of `Crystalline.exists_levelEnvelope_hom` are the envelopes of the truncations
   `P/(p)^e` of the polynomial presentation (`Crystalline.levelEnvelope`), while the levels of
   `...SmallSite.wholeSpaceSystem` are the truncations `D/(p)^{N + e}` of the *completed* envelope
   (`Crystalline.levelThickening`, through `Crystalline.uniformLevelSystem`).  Identifying the two
   families is the content of [Stacks, Tag 07KG] and [Stacks, Tag 07KH]; the tree has
   `Crystalline.completedEnvelope_isLimit` and `...SmallSite.envelopeLevelRingLimitEquiv` toward
   it and not the identification.
2. The passage from a morphism `B ⟶ T_e` to agreement of two crystal morphisms on `Γ(B, ℱ)`.
   Naturality gives agreement only on the image of `Γ(T_e, ℱ) ⟶ Γ(B, ℱ)`; reaching the whole of
   `Γ(B, ℱ)` is the crystal condition in the form "the sections over `B` are locally generated by
   the restrictions from `T_e`", which is the sections description of `SheafOfModules.pullback`
   that the tree records as missing under
   `...GlobalCrystallineSituation.FirstOrderIdealBaseChange`.
* In place of `hstep` the statements below carry hypotheses (1) and (2) of [Stacks, Tag 07JN] for
  the crystals — local quasi-coherence and local surjectivity of the closed-immersion comparison
  maps.  These are **not** stand-ins for a missing proof of the tag: they are the source's own
  standing hypotheses, which it obtains from quasi-coherence and the crystal property by
  [Stacks, Tag 07IT].  Nothing is proved about which modules satisfy
  `...SmallSite.CohomologyRestriction.IsSurjectiveComparison`, so (2) has to be carried; they are
  carried in exactly the shape `...SmallSite.computes07LG_of_sectionsComplexHomologyIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFrom07JN.lean` carries (2) for
  [Stacks, Tag 07LG], and restricted to the crystals the conclusion quantifies over.

  Hypothesis (1), local quasi-coherence, is **available**: the half of
  [Stacks, Tag 07IT] the library proves holds on the *small* site too, as
  `...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/QuasicoherentImpliesLocal.lean`, and a
  crystal in quasi-coherent modules is quasi-coherent by definition, so `hlqc F` is
  `isLocallyQuasiCoherent_of_isQuasicoherentOnSite F.obj F.property.1` and could be dropped from
  every statement below.  It is kept here only because the same `hlqc` is threaded through the
  `hdet` chain of `LevelAmbientDeterminacy.lean`, `LevelCrystalDeterminacy.lean` and
  `LevelAffineFinality.lean`, which is where it would have to be removed.
  `Computes07LGFrom07JN.lean` does not carry it.

So the faithfulness half of [Stacks, Tag 07JH] now costs exactly `hdet` on top of the hypotheses
[Stacks, Tag 07JN] is stated with, and nothing about the comparison datum, the connection, or the
four items of [Stacks, Tag 07JG].

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.14.2, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Lemma 60.5.5, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-! ### The level restrictions of the system of [Stacks, Tag 07JN], on a sheaf of modules -/

/-- **The level restriction of a sheaf of `𝒪_{X/S}`-modules along the system
`(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] is surjective**: the map

`Γ((X, T(n)_{e + 1}, δ(n)), ℱ) ⟶ Γ((X, T(n)_e, δ(n)), ℱ)`

is onto for every `n` and every `e`, under hypotheses (1) and (2) of that proposition and
nothing else.

This is the module-valued companion of `...SmallSite.surjective_wholeSpaceSystem_level_map`, which
states the same surjectivity for the underlying abelian sheaf at the coefficient universe
`u + 1`.  Neither follows from the other by unfolding: the abelian spelling is this one
universe-lifted, which is the step `...SmallSite.surjective_abelianSheaf_map_of_isIso_toX` takes,
and it is the spelling the cohomology of `Cris(X/S)` is computed in, while the module spelling is
the one the sections of the levels in [Stacks, Tag 07JG] are taken in and the one `hstep` is
about.  Both rest on the same lemma, the module-valued
`...CohomologyRestriction.surjective_presheaf_map_of_isIso_toX`, applied here at the level drops;
its three side conditions are discharged exactly as in
`...SmallSite.surjective_affineSections_level_map`: the drop
`D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}` is surjective on rings, hence a closed immersion on
ambient schemes after transport across
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, and both objects lie over the
whole of `X`. -/
theorem surjective_wholeSpaceSystem_module_level_map
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n e : ℕ) :
    Function.Surjective (F.val.map
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op) :=
  CohomologyRestriction.surjective_presheaf_map_of_isIso_toX F _ hF hM
    (isClosedImmersion_targetHom_inverse_map hp _
      (_root_.Crystalline.surjective_hom_hom_affineLevelSystem_map _ _ n (Nat.le_succ e)))
    (isWholeSpaceSystem_wholeSpaceSystem S hp n e)
    (isWholeSpaceSystem_wholeSpaceSystem S hp n (e + 1))

/-- **The one-step restrictions of a system of levels of [Stacks, Tag 07JG] are surjective.**
For a system that is the degree-zero member of `...SmallSite.wholeSpaceSystem` — which is what
the field `...SmallSite.Reduction07JG.levelSystem_isLevel` names — every one-step restriction
`Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` is onto, under hypotheses (1) and (2) of [Stacks, Tag 07JN].

This is the hypothesis `hstep` of
`...SmallSite.LevelComparison07JG.faithful_functor_of_surjective_step`, and it is
`surjective_wholeSpaceSystem_module_level_map` in degree zero. -/
theorem surjective_levelSystem_module_map_of_eq {T : ℕ ⥤ CrystallineThickening S}
    (hT : T = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (e : ℕ) :
    Function.Surjective (F.val.map (T.map (homOfLE (Nat.le_succ e))).op) := by
  subst hT
  exact surjective_wholeSpaceSystem_module_level_map hp F hF hM 0 e

/-! ### The faithfulness half with only `hdet` left -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG S D}

/-- **The faithfulness half of [Stacks, Tag 07JH] for the constructed functor, from `hdet`
alone.**

`...SmallSite.LevelComparison07JG.faithful_functor_of_surjective_step` runs on two hypotheses;
here the second, surjectivity of the one-step restrictions of the tower, is discharged by
`surjective_levelSystem_module_map_of_eq` for the system of levels [Stacks, Tag 07JN] works over.
What is left is `hdet`, that a morphism of crystals in quasi-coherent `𝒪_{X/S}`-modules is
determined by its restrictions to the levels, together with the two hypotheses of
[Stacks, Tag 07JN] on the crystals.

`hdet` is a stand-in for a result the library does not have and `hlqc`, `hsurj` are the source's
own hypotheses at [Stacks, Tag 07JN], which it derives from quasi-coherence by
[Stacks, Tag 07IT]; see the module documentation, which also records that `hlqc` is now provable
and why it is still threaded through.  **This is not [Stacks, Tag 07JH]** and no tag attribute is
placed.

`hL` is a **delimiter and not a weakening**: it is the hypothesis
`...SmallSite.LevelReduction07JG.toReduction07JG` already takes, namely the field
`...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose, and it is what makes the levels the
objects `T_e = Spec(D/(p)^{N + e})` the surjectivity above is about.  It cannot be dropped: for an
arbitrary system of levels nothing says the one-step restrictions are onto, and the field is
refuted by the degenerate system over the empty open of `X`
(`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`). -/
theorem LevelComparison07JG.faithful_functor_of_isLevel
    (C : LevelComparison07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (hdet : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) → psi = chi) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_surjective_step hdet fun F e ↦
    surjective_levelSystem_module_map_of_eq hp hL F.obj (hlqc F) (hsurj F) e

/-- **The faithfulness half of [Stacks, Tag 07JH] itself, from `hdet` alone.**  The passage from
the constructed functor to the tag's own functor costs nothing, by
`...SmallSite.faithful_functor07JG_iff`.

`hdet` is a stand-in for a result the library does not have and `hlqc`, `hsurj` are the
hypotheses of [Stacks, Tag 07JN]; the full and essentially-surjective halves of the tag are
untouched, and no tag attribute is placed. -/
theorem LevelReduction07JG.faithful_functor07JG_of_isLevel
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (hdet : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) → psi = chi) :
    Functor.Faithful (functor07JG (R.toReduction07JG (hp := hp) hL)) :=
  (faithful_functor07JG_iff (R.toReduction07JG hL)).2
    (R.toLevelComparison07JG.faithful_functor_of_isLevel hp hL hlqc hsurj hdet)

end Crystalline.GlobalCrystallineSituation.SmallSite
