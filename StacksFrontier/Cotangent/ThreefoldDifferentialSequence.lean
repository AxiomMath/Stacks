module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentials
public import StacksFrontier.Cotangent.Triangle.DifferentialSequence
public import StacksFrontier.Cotangent.ThreefoldPolynomialSite
public import StacksFrontier.RingTheory.UliftTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# Towards the differential sequence of the threefold polynomial site

Let `A → B → C` be ring maps and work on the threefold site `C_{C/B/A}` of polynomial towers
`(P → B, Q → C)` of `StacksFrontier/Cotangent/ThreefoldPolynomialSite.lean`, with its three
functors `u₁, u₂, u₃` to the two-term sites `C_{B/A}`, `C_{C/A}`, `C_{C/B}` and the three
morphisms of ringed topoi `g₁, g₂, g₃` they induce. Writing

```
Ω₁ = Ω_{𝒪/A} ⊗_𝒪 B̲   on C_{B/A},
Ω₂ = Ω_{𝒪/A} ⊗_𝒪 C̲   on C_{C/A},
Ω₃ = Ω_{𝒪/B} ⊗_𝒪 C̲   on C_{C/B},
```

Tag 08QU asserts that there is a canonical short exact sequence of sheaves of `C̲`-modules on
`C_{C/B/A}`

```
0 → g₁⁻¹Ω₁ ⊗_{B̲} C̲ → g₂⁻¹Ω₂ → g₃⁻¹Ω₃ → 0.
```

This file sets up the three sheaves, the three inverse images and the comparison data between
them, constructs the two maps of the sequence and the short complex of sheaves of `C̲`-modules
that they form, and **proves that the sequence is short exact**. The proof is the source's: the
topology of the site is chaotic, so exactness may be checked over a single polynomial tower
`(P → B, Q → C)`, and there the sequence is the split short exact sequence of Algebra,
Lemma 10.138.9 for the tower `A → P → Q` after extending scalars along the augmentation
`Q → C̲`.

Because all four sites carry the chaotic topology, every presheaf on them is a sheaf, every
construction below is taken objectwise, and no sheafification intervenes. In particular the
inverse image `gᵢ⁻¹` is restriction along `uᵢ`, which on sheaves of modules is
`PresheafOfModules.pushforward₀ uᵢ`, and the category of sheaves of `C̲`-modules on
`C_{C/B/A}` is the category of presheaves of `C̲`-modules
(`CommAlgCat.towerPresheafToSheaf`, an equivalence).

## Main definitions

* `CommAlgCat.towerConstantSheaf` and `CommAlgCat.towerConstantRingSheaf`: the constant sheaf of
  rings `C̲` on `C_{C/B/A}`, produced by Tag 08PF from the ringed point of the chaotic site.
* `CommAlgCat.towerPresheafToSheaf`: the equivalence between presheaves and sheaves of
  `C̲`-modules on `C_{C/B/A}`.
* `CommAlgCat.towerFirstOmega`, `CommAlgCat.towerSecondOmega`, `CommAlgCat.towerThirdOmega`:
  the three sheaves `Ω₁`, `Ω₂`, `Ω₃` on their respective sites.
* `CommAlgCat.towerFirstPullback`, `CommAlgCat.towerFirstTerm`,
  `CommAlgCat.towerSecondTerm`, `CommAlgCat.towerThirdTerm`: the inverse images `g₁⁻¹Ω₁`,
  `g₁⁻¹Ω₁ ⊗_{B̲} C̲`, `g₂⁻¹Ω₂` and `g₃⁻¹Ω₃`, the three terms of the sequence.
* `CommAlgCat.towerScalarHom`: the map of sheaves of rings `g₁⁻¹B̲ ⟶ C̲` along which the first
  term is base changed.
* `CommAlgCat.towerLeftRingPresheaf`, `...towerRightRingPresheaf`,
  `...towerPushoutRingPresheaf`: the three sheaves of rings `𝒪ᵢ = gᵢ⁻¹𝒪` on `C_{C/B/A}`, and
  `CommAlgCat.towerLeftToRight`, `CommAlgCat.towerRightToPushout`: the maps `𝒪₁ ⟶ 𝒪₂ ⟶ 𝒪₃`
  given by `P → Q → Q ⊗_P B`.
* `CommAlgCat.towerFirstOmegaPullback`, `...towerSecondOmegaPullback`,
  `...towerThirdOmegaPullback`: the inverse images of the sheaves of relative differentials
  `Ω_{𝒪/A}`, `Ω_{𝒪/A}`, `Ω_{𝒪/B}`, each again a presheaf of relative differentials and so
  carrying a universal derivation.
* `CommAlgCat.derivationComp`: a derivation transported along a map of presheaves of rings and
  a semilinear natural family of maps; this is the tool with which the two maps of the sequence
  are constructed.
* `CommAlgCat.changeOfRingsUnit`: the unit `z ↦ 1 ⊗ z` of the change-of-rings adjunction of
  Tag 03CU on sections, as an additive map. This is the semilinear natural family that
  `CommAlgCat.derivationComp` is fed.
* `CommAlgCat.towerFirstDerivation` and `CommAlgCat.towerSecondDerivation`: the derivations
  `p ↦ 1 ⊗ d p` of `𝒪₁` and `q ↦ 1 ⊗ d(1 ⊗ q)` of `𝒪₂` that give the two maps.
* `CommAlgCat.towerFirstSequenceMap` and `CommAlgCat.towerSecondSequenceMap`: the two maps
  `g₁⁻¹Ω₁ ⊗_{B̲} C̲ ⟶ g₂⁻¹Ω₂` and `g₂⁻¹Ω₂ ⟶ g₃⁻¹Ω₃` of the sequence of Tag 08QU.
* `CommAlgCat.towerShortComplexPresheaf` and `CommAlgCat.towerShortComplex`: the sequence as a
  short complex of presheaves and as a short complex of sheaves of `C̲`-modules on `C_{C/B/A}`.

## Main results

* `CommAlgCat.towerDifferential_shortExact_extendScalars`: for a tower `R → P → Q` with `Q`
  formally smooth over `P`, the split short exact sequence
  `0 → Q ⊗_P Ω_{P/R} → Ω_{Q/R} → Ω_{Q/P} → 0` of Algebra, Lemma 10.138.9 stays short exact
  after extending scalars along an arbitrary ring map `Q → S`. This is the objectwise input to
  the exactness asserted by Tag 08QU.
* `CommAlgCat.towerSections_formallySmooth` and `CommAlgCat.towerSections_isPushout`: the two
  ring-theoretic inputs to that exactness, read on the universe-lifted sections over a polynomial
  tower — the sections of `𝒪₂` are formally smooth over those of `𝒪₁`, and the square
  `𝒪₁ → B̲`, `𝒪₁ → 𝒪₂`, `B̲ → 𝒪₃`, `𝒪₂ → 𝒪₃` is a pushout square.
* `CommAlgCat.towerConstantSheaf_eq_second` and `CommAlgCat.towerConstantSheaf_eq_third`: the
  inverse images along `g₂` and `g₃` of the constant sheaf `C̲` are the constant sheaf `C̲` on
  `C_{C/B/A}` — on the nose, not merely up to isomorphism.
* `CommAlgCat.towerFirstPullback_eq`, `CommAlgCat.towerSecondTerm_eq`,
  `CommAlgCat.towerThirdTerm_eq`: each term is the objectwise base change of the inverse image
  of the sheaf of relative differentials.
* `CommAlgCat.towerSecondTerm_obj`: on sections the second term is the extension of scalars of
  `Ω[Q⁄A]` along the augmentation `Q → C̲(W)`, i.e. on the nose the middle term of
  `CommAlgCat.towerDifferential_shortExact_extendScalars`.
* `CommAlgCat.towerScalarHom_app_towerFirstAug`: the tower condition on sections, `P → B → C`
  is `P → Q → C`.
* `CommAlgCat.towerThirdAug_app_towerRightToPushout`: `Q → Q ⊗_P B → C` is `Q → C`.
* `CommAlgCat.towerRightToPushout_app_towerLeftToRight`: the pushout square on sections,
  `P → Q → Q ⊗_P B` is `P → B → Q ⊗_P B`; this is what will make the composite of the two maps
  of the sequence vanish.
* `CommAlgCat.towerLeftToRight_app_towerFirstBaseHom`: `A → P → Q` is `A → Q`.
* `CommAlgCat.towerSequenceMap_comp`: the composite of the two maps of the sequence vanishes,
  so that they form a short complex.
* `CommAlgCat.towerShortComplex_shortExact_of_objectwise`: consequently the exactness asserted
  by Tag 08QU follows from the exactness of the sequence of sections over a polynomial tower.
* `CommAlgCat.baseChange_linearMap_ext`, `CommAlgCat.baseChange_kaehler_ext` and
  `CommAlgCat.doubleBaseChange_kaehler_ext`: two linear maps out of `S ⊗[R] N`,
  `S ⊗[R] Ω_{R/R₀}` or `S ⊗[A] (A ⊗[R] Ω_{R/R₀})` agree as soon as they agree on `1 ⊗ n`,
  on `1 ⊗ d r` or on `1 ⊗ 1 ⊗ d r`. These are the criteria by which the two squares
  identifying the sequence of sections with the objectwise split sequence are checked.
* `CommAlgCat.towerShortComplexPresheaf_shortExact_obj`: the sequence of sections over a
  polynomial tower is short exact — the objectwise form of Tag 08QU.
* `CommAlgCat.towerShortComplex_shortExact`: **Tag 08QU**, the sequence of sheaves of
  `C̲`-modules on `C_{C/B/A}` is short exact.

## Implementation notes

**Why the inverse images of the constant sheaves agree on the nose.** `C̲` on `C_{C/A}` is
`π₂⁻¹C` and `C̲` on `C_{C/B/A}` is `π⁻¹C`, and Tag 08QT proves `π = π₂ ∘ g₂` with the inverse
images equal by `rfl`. Since the ring carried on the point is `ULift C` for both sites, the two
constant sheaves of rings are literally the same functor, and likewise for `g₃`. This is what
lets all three terms of the sequence be presheaves of modules over one and the same sheaf of
rings with no transport, and it is also why the two identifications
`CommAlgCat.polynomialConstantSheafIso` of the constant sheaves of `C_{C/A}` and of `C_{C/B}`
with the constant presheaf agree at the objects in question.

**The shape of the two maps.** All three terms are of the form `changeOfRings aug (gᵢ⁻¹Ω)` with
`gᵢ⁻¹Ω` again a presheaf of relative differentials (`towerSecondTerm_eq` and its siblings), so
by the change-of-rings adjunction of Tag 03CU and the universal property of
`PresheafOfModules.DifferentialsConstruction.relativeDifferentials'` a map out of a term is the
same datum as a *derivation*. The derivation that gives the second map sends a section `q` of
`𝒪₂` to `1 ⊗ d(1 ⊗ q)`, and the one that gives the first map sends a section `p` of `𝒪₁` to
`1 ⊗ d(p)`; `CommAlgCat.derivationComp` is the general construction producing them from the
universal derivations of `Ω_{𝒪/B}` and `Ω_{𝒪/A}` together with `CommAlgCat.changeOfRingsUnit`,
the unit of the change-of-rings adjunction, with the compatibilities above supplying its
hypotheses. This reduces the construction of the two maps to element-level computations and
avoids any naturality square. The same unit makes the vanishing of the composite an identity
between derivations: `CommAlgCat.changeOfRingsHom_eq_zero` says that a map out of a change of
rings vanishes as soon as it kills the sections `1 ⊗ z`, which the adjunction of Tag 03CU gives
with no induction on tensors, and the derivation one is left with kills `d` of a section of
`𝒪₁` because that section's image in `𝒪₃` comes from `B̲`.

**Universes in the change of rings.** The module universe of
`Stacks.PresheafOfModules.ChangeOfRings.restrictScalars` and of `changeOfRings` is not
determined by their arguments, so an occurrence of either whose universes are left to
unification stops the elaborator at the constraint `max (u + 1) ?u =?= u + 1`. Every occurrence
below therefore carries its universes explicitly, as `restrictScalars.{u + 1, u, u + 1, u + 1}`
and `counitHom.{u + 1, u, u + 1, u + 1}`.

**Spellings of the constant sheaf of rings.** `CommAlgCat.towerConstantSheaf` is reducible only
through `fibredSituation`, so the sheaf of rings over which `CommAlgCat.towerSecondTerm` is
declared and the one in the target of `CommAlgCat.towerSecondAug` are equal by `rfl` but not
syntactically. A statement mixing the two is not type-correct at the `implicit` transparency
level at which `rw` builds its motive, so the objectwise hypotheses of
`CommAlgCat.derivationComp` and the last step of `CommAlgCat.towerSequenceMap_comp` are supplied
as terms, through `congrArg` and `Eq.trans`, rather than by rewriting.

**How the sequence of sections is identified with the split sequence.** Over a polynomial tower
`(P → B, Q → C)`, with `T = Q ⊗_P B` and every ring replaced by its universe lift, the three
modules of sections are `C̲(W) ⊗_{B̲(W)} (B̲(W) ⊗_P Ω_{P/A})`, `C̲(W) ⊗_Q Ω_{Q/A}` and
`C̲(W) ⊗_T Ω_{T/B}`, and they are matched with the three terms of
`CommAlgCat.towerDifferential_shortExact_extendScalars` for the tower `A → P → Q` and the
augmentation `ε : Q → C̲(W)`. Taking `S := C̲(W)` itself, rather than `ULift C`, makes the
base-change ring the actual ring of sections, so that the comparison
`CommAlgCat.polynomialConstantSheafIso` of the constant sheaf with the constant presheaf never
enters. The middle term then needs no identification at all: `CommAlgCat.towerSecondTerm_obj`
says it is the middle term of the objectwise sequence on the nose. The first terms are matched
by cancelling the base change twice, through `C̲(W) ⊗_P Ω_{P/A}`, and the third ones by
`KaehlerDifferential.tensorKaehlerEquiv` followed by one more cancellation.

The ring-theoretic inputs are `CommAlgCat.towerSections_formallySmooth`, which is
`Algebra.FormallySmooth (ULift P) (ULift Q)`, and `CommAlgCat.towerSections_isPushout`, which is
`Algebra.IsPushout (ULift P) (ULift B) (ULift Q) (ULift T)` — both by way of
`StacksFrontier/RingTheory/UliftTransport.lean`, which states them for an arbitrary universe lift.
Those two files state the pushout square for the algebra structures `ULift.algebra'`, whereas
the structures the sheaves of rings carry come from the maps `𝒪₁ ⟶ 𝒪₂ ⟶ 𝒪₃` by
`RingHom.toAlgebra`; `Algebra.uliftTensorProductEquiv'` is the form of the comparison
isomorphism that accepts a prescribed structure, and with `Algebra.IsPushout.of_equiv` it
transports the square to the structures in use. Besides those two inputs the identification
needs the three scalar towers `IsScalarTower (ULift P) (g₁⁻¹B̲(W)) (C̲(W))` (by `rfl`),
`IsScalarTower (ULift P) (ULift Q) (C̲(W))` (this is
`CommAlgCat.towerScalarHom_app_towerFirstAug`) and `IsScalarTower (ULift Q) (ULift T) (C̲(W))`
(this is `CommAlgCat.towerThirdAug_app_towerRightToPushout`), and the two commuting squares,
which by `CommAlgCat.doubleBaseChange_kaehler_ext` and `CommAlgCat.baseChange_kaehler_ext`
reduce to the computation of the two maps on the generators `1 ⊗ 1 ⊗ d p` and `1 ⊗ d q`, namely
`1 ⊗ 1 ⊗ d p ↦ 1 ⊗ d (image of p in Q)` and `1 ⊗ d q ↦ 1 ⊗ d (1 ⊗ q)`. Those two computations
are `CommAlgCat.counitHom_app_changeOfRingsUnit` applied twice and once, with no induction on
tensors.

## References

* [Stacks Project, Tag 08QU](https://stacks.math.columbia.edu/tag/08QU)
* [Stacks Project, Section 08QR](https://stacks.math.columbia.edu/tag/08QR)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u w v₁ u₁

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-! ### The split differential sequence of a formally smooth extension -/

/-- For a tower `R → P → Q` with `Q` formally smooth over `P`, the differential sequence
`0 → Q ⊗_P Ω_{P/R} → Ω_{Q/R} → Ω_{Q/P} → 0` of Algebra, Lemma 10.138.9 is split, so it stays
short exact after extending scalars along an arbitrary ring map `ε : Q → S`. This is the
objectwise input to the exactness of the sequence of Tag 08QU. -/
@[stacks 08QU "the objectwise split differential sequence after base change: the exactness \
  input of the lemma, at an object of the site"]
theorem towerDifferential_shortExact_extendScalars
    (R P Q S : Type w) [CommRing R] [CommRing P] [CommRing Q] [CommRing S]
    [Algebra R P] [Algebra P Q] [Algebra R Q] [IsScalarTower R P Q]
    [Algebra.FormallySmooth P Q] (ε : Q →+* S) :
    ((ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange R P Q)
        (KaehlerDifferential.map R P Q Q) (by
          apply LinearMap.ext
          intro x
          exact (KaehlerDifferential.exact_mapBaseChange_map R P Q).apply_apply_eq_zero x)).map
      (ModuleCat.extendScalars ε)).ShortExact := by
  let S₀ := ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange R P Q)
    (KaehlerDifferential.map R P Q Q) (LinearMap.ext fun x =>
      (KaehlerDifferential.exact_mapBaseChange_map R P Q).apply_apply_eq_zero x)
  have hS : S₀.ShortExact := towerDifferential_shortExact.{w, w} R P Q
  obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange R P Q
  have sp : S₀.Splitting := .ofExactOfRetraction S₀ hS.exact (ModuleCat.ofHom r)
    (ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.congr_fun hr x)) hS.epi_g
  let F := ModuleCat.extendScalars ε
  have : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj ε).isLeftAdjoint
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  exact (sp.map F).shortExact

/-! ### The constant sheaf of rings `C̲` on the threefold site -/

/-- Every presheaf on `C_{C/B/A}` is a sheaf, because the topology of the site is chaotic. -/
@[stacks 08QU "exactness may be checked objectwise: every presheaf on the threefold site is \
  a sheaf"]
theorem isSheaf_polynomialTowerTopology {D : Type*} [Category D]
    (F : (polynomialTowerSite A B C)ᵒᵖ ⥤ D) :
    Presheaf.IsSheaf (polynomialTowerTopology A B C) F := by
  rw [polynomialTowerTopology_eq_bot A B C]
  exact Presheaf.isSheaf_bot _

/-- The constant sheaf of rings `C̲` on `C_{C/B/A}`, produced by Tag 08PF from the ringed point
of the chaotic site. -/
def towerConstantSheaf : Sheaf (polynomialTowerTopology A B C) CommRingCat.{u + 1} :=
  (polynomialTowerRingedPoint A B C).constantRingSheaf

/-- `C̲` with commutativity of its values forgotten; sheaves of `C̲`-modules are taken over
this sheaf of rings. -/
abbrev towerConstantRingSheaf : Sheaf (polynomialTowerTopology A B C) RingCat.{u + 1} :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (towerConstantSheaf A B C)

/-- `C̲` on `C_{C/B/A}` is the inverse image along `g₂` of the constant sheaf `C̲` on
`C_{C/A}`: both are the inverse image of the ring `C` on the point, and `π = π₂ ∘ g₂`. -/
theorem towerConstantSheaf_eq_second :
    (polynomialTowerSecond A B C).op ⋙ (polynomialConstantSheaf A (towerTotalAlgebra A C)).obj =
      (towerConstantSheaf A B C).obj := rfl

/-- `C̲` on `C_{C/B/A}` is the inverse image along `g₃` of the constant sheaf `C̲` on
`C_{C/B}`. -/
theorem towerConstantSheaf_eq_third :
    (polynomialTowerThird A B C).op ⋙ (polynomialConstantSheaf B (towerRelativeAlgebra B C)).obj =
      (towerConstantSheaf A B C).obj := rfl

/-- The category of sheaves of `C̲`-modules on `C_{C/B/A}` is the category of presheaves of
`C̲`-modules: the topology is chaotic, so the sheaf condition is vacuous. -/
def towerPresheafToSheaf :
    PresheafOfModules.{u + 1} (towerConstantRingSheaf A B C).obj ⥤
      SheafOfModules.{u + 1} (towerConstantRingSheaf A B C) where
  obj M := { val := M, isSheaf := isSheaf_polynomialTowerTopology A B C _ }
  map f := ⟨f⟩

/-- The functor `towerPresheafToSheaf` is full. -/
instance : (towerPresheafToSheaf A B C).Full where
  map_surjective f := ⟨f.val, rfl⟩

/-- The functor `towerPresheafToSheaf` is faithful. -/
instance : (towerPresheafToSheaf A B C).Faithful where
  map_injective h := congrArg SheafOfModules.Hom.val h

/-- The functor `towerPresheafToSheaf` is essentially surjective. -/
instance : (towerPresheafToSheaf A B C).EssSurj where
  mem_essImage N := ⟨N.val, ⟨Iso.refl _⟩⟩

/-- The functor `towerPresheafToSheaf` from presheaves to sheaves of `C̲`-modules on
`C_{C/B/A}` is an equivalence of categories. -/
instance : (towerPresheafToSheaf A B C).IsEquivalence where

/-- The functor `towerPresheafToSheaf` is additive. -/
instance : (towerPresheafToSheaf A B C).Additive where

/-! ### The three sheaves of differentials -/

/-- `Ω₁ = Ω_{𝒪/A} ⊗_𝒪 B̲`, the sheaf of `B̲`-modules on `C_{B/A}`. -/
@[stacks 08QU "the sheaf Ω₁ = Ω_{𝒪/A} ⊗_𝒪 B̲ on C_{B/A}"]
abbrev towerFirstOmega : SheafOfModules.{u + 1} (polynomialConstantRingSheaf A
    (towerBaseAlgebra A B)) :=
  polynomialRelativeDifferentialsBaseChange A (towerBaseAlgebra A B)

/-- `Ω₂ = Ω_{𝒪/A} ⊗_𝒪 C̲`, the sheaf of `C̲`-modules on `C_{C/A}`. -/
@[stacks 08QU "the sheaf Ω₂ = Ω_{𝒪/A} ⊗_𝒪 C̲ on C_{C/A}"]
abbrev towerSecondOmega : SheafOfModules.{u + 1} (polynomialConstantRingSheaf A
    (towerTotalAlgebra A C)) :=
  polynomialRelativeDifferentialsBaseChange A (towerTotalAlgebra A C)

/-- `Ω₃ = Ω_{𝒪/B} ⊗_𝒪 C̲`, the sheaf of `C̲`-modules on `C_{C/B}`. -/
@[stacks 08QU "the sheaf Ω₃ = Ω_{𝒪/B} ⊗_𝒪 C̲ on C_{C/B}"]
abbrev towerThirdOmega : SheafOfModules.{u + 1} (polynomialConstantRingSheaf B
    (towerRelativeAlgebra B C)) :=
  polynomialRelativeDifferentialsBaseChange B (towerRelativeAlgebra B C)

/-! ### The inverse images and the scalar map `g₁⁻¹B̲ ⟶ C̲` -/

/-- `g₁⁻¹B̲`, the inverse image along `g₁` of the constant sheaf `B̲` of `C_{B/A}`. -/
abbrev towerBaseConstantPresheaf : (polynomialTowerSite A B C)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (polynomialTowerFirst A B C).op ⋙ (polynomialConstantSheaf A (towerBaseAlgebra A B)).obj

/-- The map of sheaves of rings `g₁⁻¹B̲ ⟶ C̲` on `C_{C/B/A}` induced by `B → C`. -/
def towerScalarHom : towerBaseConstantPresheaf A B C ⟶ (towerConstantSheaf A B C).obj :=
  Functor.whiskerLeft (polynomialTowerFirst A B C).op
      (polynomialConstantSheafIso A (towerBaseAlgebra A B)).hom ≫
    (Functor.const (polynomialTowerSite A B C)ᵒᵖ).map
      (CommRingCat.ofHom (KaehlerDifferential.uliftAlgebraMap.{u, u + 1} B C)) ≫
    Functor.whiskerLeft (polynomialTowerSecond A B C).op
      (polynomialConstantSheafIso A (towerTotalAlgebra A C)).inv

/-- The map `g₁⁻¹B̲ ⟶ C̲` on sections: read through the identifications of the two constant
sheaves with the constant presheaves, it is the universe lift of `B → C`. -/
theorem towerScalarHom_app (W : (polynomialTowerSite A B C)ᵒᵖ)
    (b : (towerBaseConstantPresheaf A B C).obj W) :
    (towerScalarHom A B C).app W b =
      (polynomialConstantSheafIso A (towerTotalAlgebra A C)).inv.app
          ((polynomialTowerSecond A B C).op.obj W)
        (ULift.up (algebraMap B C
          ((polynomialConstantSheafIso A (towerBaseAlgebra A B)).hom.app
            ((polynomialTowerFirst A B C).op.obj W) b).down)) := rfl

/-- `g₂⁻¹Ω₂`, a presheaf of `C̲`-modules on `C_{C/B/A}`: the inverse image along `g₂` is
restriction along `u₂`, and the inverse image of `C̲` is `C̲`. -/
@[stacks 08QU "the second term g₂⁻¹Ω₂ of the sequence"]
def towerSecondTerm : PresheafOfModules.{u + 1} (towerConstantRingSheaf A B C).obj :=
  (PresheafOfModules.pushforward₀ (polynomialTowerSecond A B C)
    (polynomialConstantRingSheaf A (towerTotalAlgebra A C)).obj).obj (towerSecondOmega A C).val

/-- `g₃⁻¹Ω₃`, a presheaf of `C̲`-modules on `C_{C/B/A}`. -/
@[stacks 08QU "the third term g₃⁻¹Ω₃ of the sequence"]
def towerThirdTerm : PresheafOfModules.{u + 1} (towerConstantRingSheaf A B C).obj :=
  (PresheafOfModules.pushforward₀ (polynomialTowerThird A B C)
    (polynomialConstantRingSheaf B (towerRelativeAlgebra B C)).obj).obj (towerThirdOmega B C).val

/-- `g₁⁻¹Ω₁`, a presheaf of `g₁⁻¹B̲`-modules on `C_{C/B/A}`. -/
def towerFirstPullback : PresheafOfModules.{u + 1}
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      (towerBaseConstantPresheaf A B C)) :=
  (PresheafOfModules.pushforward₀ (polynomialTowerFirst A B C)
    (polynomialConstantRingSheaf A (towerBaseAlgebra A B)).obj).obj (towerFirstOmega A B).val

/-- `g₁⁻¹Ω₁ ⊗_{B̲} C̲`, a presheaf of `C̲`-modules on `C_{C/B/A}`. -/
@[stacks 08QU "the first term g₁⁻¹Ω₁ ⊗_{B̲} C̲ of the sequence"]
def towerFirstTerm : PresheafOfModules.{u + 1} (towerConstantRingSheaf A B C).obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (towerScalarHom A B C)).obj
    (towerFirstPullback A B C)

/-! ### The three structure sheaves on the threefold site and the maps between them -/

/-- The universe lift of a ring map between algebras whose sections live in `Type u`, in the
universe in which the sheaves of rings of the sites take their values. -/
abbrev uliftRingHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    ULift.{u + 1} R →+* ULift.{u + 1} S :=
  ((ULift.ringEquiv : ULift.{u + 1} S ≃+* S).symm.toRingHom).comp
    (f.comp (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom)

/-- `𝒪₁ = g₁⁻¹𝒪`, as a presheaf of commutative rings on `C_{C/B/A}`: its sections over the
tower `(P → B, Q → C)` are `P`. -/
abbrev towerLeftRingPresheaf : (polynomialTowerSite A B C)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (polynomialTowerFirst A B C).op ⋙ (polynomialStructureSheaf A (towerBaseAlgebra A B)).obj

/-- `𝒪₂ = g₂⁻¹𝒪`: its sections over `(P → B, Q → C)` are `Q`. -/
abbrev towerRightRingPresheaf : (polynomialTowerSite A B C)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (polynomialTowerSecond A B C).op ⋙ (polynomialStructureSheaf A (towerTotalAlgebra A C)).obj

/-- `𝒪₃ = g₃⁻¹𝒪`: its sections over `(P → B, Q → C)` are `Q ⊗_P B`. -/
abbrev towerPushoutRingPresheaf : (polynomialTowerSite A B C)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (polynomialTowerThird A B C).op ⋙ (polynomialStructureSheaf B (towerRelativeAlgebra B C)).obj

/-- The map of sheaves of rings `𝒪₁ ⟶ 𝒪₂` on `C_{C/B/A}` given by the map `P → Q` of a
polynomial tower. -/
def towerLeftToRight : towerLeftRingPresheaf A B C ⟶ towerRightRingPresheaf A B C where
  app W := CommRingCat.ofHom
    (uliftRingHom (CommAlgCat.Hom.hom W.unop.unop.obj.hom).toRingHom)
  naturality W X f := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ULift.ext _ _ ?_)
    exact (towerRight_hom_apply f.unop.unop.hom p.down).symm

/-- The map of sheaves of rings `𝒪₂ ⟶ 𝒪₃` on `C_{C/B/A}` given by `q ↦ 1 ⊗ q`, the second leg
of the pushout square defining `u₃`. -/
def towerRightToPushout : towerRightRingPresheaf A B C ⟶ towerPushoutRingPresheaf A B C where
  app W := CommRingCat.ofHom (uliftRingHom
    (Algebra.TensorProduct.includeRight (R := ↑(towerLeftAlgebra W.unop.unop.obj))
      (A := B) (B := ↑(towerRightAlgebra W.unop.unop.obj))).toRingHom)
  naturality W X f := by
    refine CommRingCat.hom_ext (RingHom.ext fun q => ULift.ext _ _ ?_)
    exact (towerBaseChangeMap_tmul f.unop.unop.hom 1 q.down).symm

/-! ### The two universe-lifted ring-theoretic inputs over a polynomial tower -/

/-- **The map `𝒪₁ ⟶ 𝒪₂` on sections is the universe lift of the map `P → Q` of the tower.**
In particular the `𝒪₁(W)`-algebra structure it puts on `𝒪₂(W)` is the universe lift of the
`P`-algebra structure of `Q`. -/
theorem towerLeftToRight_app_hom (W : (polynomialTowerSite A B C)ᵒᵖ) :
    ((towerLeftToRight A B C).app W).hom =
      RingHom.ulift.{u + 1, u + 1}
        (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj)
          ↑(towerRightAlgebra W.unop.unop.obj)) :=
  rfl

/-- **The sections of `𝒪₂` are formally smooth over the sections of `𝒪₁`.** Over the tower
`(P → B, Q → C)` the map is the universe lift of `P → Q`, and `Q` is a polynomial algebra over
`P` by the first condition on a polynomial tower, hence formally smooth over `P`; formal
smoothness survives the universe lift by `RingHom.FormallySmooth.ulift`. This is the hypothesis
`Algebra.FormallySmooth` that `CommAlgCat.towerDifferential_shortExact_extendScalars` needs at
the object `W` of `C_{C/B/A}`. -/
@[stacks 08QU "the sections of 𝒪₂ are formally smooth over the sections of 𝒪₁: the formal \
  smoothness input of the objectwise differential sequence"]
theorem towerSections_formallySmooth (W : (polynomialTowerSite A B C)ᵒᵖ) :
    letI := ((towerLeftToRight A B C).app W).hom.toAlgebra
    Algebra.FormallySmooth ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) := by
  obtain ⟨κ, ⟨e⟩⟩ := W.unop.unop.property.1
  have hsmooth : Algebra.FormallySmooth ↑(towerLeftAlgebra W.unop.unop.obj)
      ↑(towerRightAlgebra W.unop.unop.obj) := Algebra.FormallySmooth.of_equiv e
  exact RingHom.FormallySmooth.ulift (RingHom.formallySmooth_algebraMap.2 hsmooth)

attribute [local instance] ULift.algebra' Algebra.TensorProduct.rightAlgebra in
/-- **The pushout square of a polynomial tower survives the universe lift.** The sections of
`𝒪₃` over the tower `(P → B, Q → C)` are `Q ⊗_P B`, so the square `P → B`, `P → Q`, `B → Q ⊗_P B`,
`Q → Q ⊗_P B` of the tower is a pushout square of rings; `Algebra.IsPushout.ulift_tensorProduct`
transports that to the universe lifts, which is the form in which the sections of the three
structure sheaves carry it. This is the hypothesis `Algebra.IsPushout` that
`KaehlerDifferential.tensorKaehlerEquiv` needs in order to identify `Ω_{𝒪₃/B̲}` with
`𝒪₃ ⊗_{𝒪₂} Ω_{𝒪₂/𝒪₁}` on sections. -/
@[stacks 08QU "the pushout square of the tower on the universe-lifted sections: the input that \
  identifies the third term of the objectwise sequence"]
theorem towerSections_isPushout (W : (polynomialTowerSite A B C)ᵒᵖ) :
    Algebra.IsPushout (ULift.{u + 1} ↑(towerLeftAlgebra W.unop.unop.obj)) (ULift.{u + 1} B)
      (ULift.{u + 1} ↑(towerRightAlgebra W.unop.unop.obj))
      (ULift.{u + 1} ↑(towerBaseChangeAlgebra W.unop.unop.obj)) :=
  Algebra.IsPushout.ulift_tensorProduct.{u, u + 1} ↑(towerLeftAlgebra W.unop.unop.obj) B
    ↑(towerRightAlgebra W.unop.unop.obj)

/-! ### The pulled-back base maps and augmentations -/

section

open PresheafOfModules.DifferentialsConstruction

/-- `g₁⁻¹(A̲ ⟶ 𝒪)`, the base map of `C_{B/A}` pulled back to `C_{C/B/A}`. -/
abbrev towerFirstBaseHom :=
  Functor.whiskerLeft (polynomialTowerFirst A B C).op
    (polynomialBaseStructureHom A (towerBaseAlgebra A B)).hom

/-- `g₂⁻¹(A̲ ⟶ 𝒪)`. -/
abbrev towerSecondBaseHom :=
  Functor.whiskerLeft (polynomialTowerSecond A B C).op
    (polynomialBaseStructureHom A (towerTotalAlgebra A C)).hom

/-- `g₃⁻¹(B̲ ⟶ 𝒪)`. -/
abbrev towerThirdBaseHom :=
  Functor.whiskerLeft (polynomialTowerThird A B C).op
    (polynomialBaseStructureHom B (towerRelativeAlgebra B C)).hom

/-- `g₁⁻¹(𝒪 ⟶ B̲)`, the augmentation of `C_{B/A}` pulled back to `C_{C/B/A}`. -/
abbrev towerFirstAug :=
  Functor.whiskerLeft (polynomialTowerFirst A B C).op
    (polynomialAugmentation A (towerBaseAlgebra A B)).hom

/-- `g₂⁻¹(𝒪 ⟶ C̲)`. -/
abbrev towerSecondAug :=
  Functor.whiskerLeft (polynomialTowerSecond A B C).op
    (polynomialAugmentation A (towerTotalAlgebra A C)).hom

/-- `g₃⁻¹(𝒪 ⟶ C̲)`. -/
abbrev towerThirdAug :=
  Functor.whiskerLeft (polynomialTowerThird A B C).op
    (polynomialAugmentation B (towerRelativeAlgebra B C)).hom

/-- `g₁⁻¹Ω_{𝒪/A}`, a presheaf of `𝒪₁`-modules on `C_{C/B/A}`. Pulling back the presheaf of
relative differentials along `u₁` is the presheaf of relative differentials of the pulled-back
map of presheaves of rings, so it carries a universal derivation. -/
abbrev towerFirstOmegaPullback := relativeDifferentials' (towerFirstBaseHom A B C)

/-- `g₂⁻¹Ω_{𝒪/A}`, a presheaf of `𝒪₂`-modules on `C_{C/B/A}`. -/
abbrev towerSecondOmegaPullback := relativeDifferentials' (towerSecondBaseHom A B C)

/-- `g₃⁻¹Ω_{𝒪/B}`, a presheaf of `𝒪₃`-modules on `C_{C/B/A}`. -/
abbrev towerThirdOmegaPullback := relativeDifferentials' (towerThirdBaseHom A B C)

end

section

open PresheafOfModules.DifferentialsConstruction

/-- `g₁⁻¹Ω₁` is the base change of `g₁⁻¹Ω_{𝒪/A}` along `g₁⁻¹(𝒪 ⟶ B̲)`: the inverse image is
restriction along `u₁`, and both base change and differentials are formed objectwise. -/
theorem towerFirstPullback_eq : towerFirstPullback A B C =
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (towerFirstAug A B C)).obj
      (towerFirstOmegaPullback A B C) := rfl

/-- `g₂⁻¹Ω₂` is the base change of `g₂⁻¹Ω_{𝒪/A}` along `g₂⁻¹(𝒪 ⟶ C̲)`. -/
theorem towerSecondTerm_eq : towerSecondTerm A B C =
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (towerSecondAug A B C)).obj
      (towerSecondOmegaPullback A B C) := rfl

/-- **The sections of `g₂⁻¹Ω₂` over an object of `C_{C/B/A}` are the middle term of the objectwise
differential sequence.** Over the tower `(P → B, Q → C)` they are `C̲(W) ⊗_Q Ω[Q⁄A]`, which is on
the nose the middle term of `CommAlgCat.towerDifferential_shortExact_extendScalars` for the tower
`A̲ → 𝒪₁ → 𝒪₂` of sections and the augmentation `𝒪₂(W) → C̲(W)`: both the tensor product and the
algebra structure on `C̲(W)` are the ones the augmentation induces. -/
theorem towerSecondTerm_obj (W : (polynomialTowerSite A B C)ᵒᵖ) :
    (towerSecondTerm A B C).obj W =
      (ModuleCat.extendScalars ((towerSecondAug A B C).app W).hom).obj
        (CommRingCat.KaehlerDifferential ((towerSecondBaseHom A B C).app W)) :=
  rfl

/-- `g₃⁻¹Ω₃` is the base change of `g₃⁻¹Ω_{𝒪/B}` along `g₃⁻¹(𝒪 ⟶ C̲)`. -/
theorem towerThirdTerm_eq : towerThirdTerm A B C =
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (towerThirdAug A B C)).obj
      (towerThirdOmegaPullback A B C) := rfl

end

/-- The augmentation of `C_{D/A}` on sections, composed with the identification of the constant
sheaf with the constant presheaf, is the universe-lifted augmentation `α` of the object. -/
theorem polynomialAugmentation_app_apply' {D : CommAlgCat.{u} A}
    (X : (polynomialSite A D)ᵒᵖ) (x : (polynomialStructureSheaf A D).obj.obj X) :
    (polynomialConstantSheafIso A D).hom.app X
        ((polynomialAugmentation A D).hom.app X x) =
      (polynomialAugmentationPresheaf A D).app X x := by
  have hx := congrArg (fun k : CommRingCat.Hom _ _ => k.hom x)
    (polynomialAugmentation_app A D X.unop)
  simp only [CommRingCat.comp_apply] at hx
  exact hx

/-- The augmentation of `C_{D/A}` on sections, read through the identification of the constant
sheaf with the constant presheaf: it is the augmentation `α` of the object, universe-lifted. -/
theorem polynomialAugmentation_app_apply {D : CommAlgCat.{u} A}
    (X : (polynomialSite A D)ᵒᵖ) (x : (polynomialStructureSheaf A D).obj.obj X) :
    (polynomialAugmentation A D).hom.app X x =
      (polynomialConstantSheafIso A D).inv.app X
        ((polynomialAugmentationPresheaf A D).app X x) := by
  rw [← polynomialAugmentation_app_apply']
  simp

/-! ### The compatibilities of the three structure sheaves with the augmentations -/

/-- **The tower condition on sections.** The two maps `𝒪₁ ⟶ C̲`, through the augmentation
`𝒪₁ ⟶ B̲` followed by `B̲ ⟶ C̲` and through `𝒪₁ ⟶ 𝒪₂` followed by the augmentation
`𝒪₂ ⟶ C̲`, agree: both are `P → C`. -/
theorem towerScalarHom_app_towerFirstAug (W : (polynomialTowerSite A B C)ᵒᵖ)
    (p : (towerLeftRingPresheaf A B C).obj W) :
    (towerScalarHom A B C).app W ((towerFirstAug A B C).app W p) =
      (towerSecondAug A B C).app W ((towerLeftToRight A B C).app W p) := by
  simp only [towerFirstAug, towerSecondAug, Functor.whiskerLeft_app]
  rw [towerScalarHom_app, polynomialAugmentation_app_apply', polynomialAugmentation_app_apply]
  refine congrArg _ (ULift.ext _ _ ?_)
  exact (towerRight_hom_towerMap_apply W.unop.unop p.down).symm

/-- The augmentation `𝒪₃ ⟶ C̲` restricted along `𝒪₂ ⟶ 𝒪₃` is the augmentation `𝒪₂ ⟶ C̲`:
the map `Q ⊗_P B → C` sends `1 ⊗ q` to the image of `q`. -/
theorem towerThirdAug_app_towerRightToPushout (W : (polynomialTowerSite A B C)ᵒᵖ)
    (q : (towerRightRingPresheaf A B C).obj W) :
    (towerThirdAug A B C).app W ((towerRightToPushout A B C).app W q) =
      (towerSecondAug A B C).app W q := by
  simp only [towerThirdAug, towerSecondAug, Functor.whiskerLeft_app]
  rw [polynomialAugmentation_app_apply, polynomialAugmentation_app_apply]
  refine congrArg _ (ULift.ext _ _ ?_)
  change towerBaseChangeAugmentation W.unop.unop
      ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.unop.unop.obj)] q.down) = _
  refine (towerBaseChangeAugmentation_tmul W.unop.unop 1 q.down).trans ?_
  rw [map_one, one_mul]
  rfl

/-- The map `𝒪₁ ⟶ 𝒪₂` followed by the base map `A̲ ⟶ 𝒪₁` is the base map `A̲ ⟶ 𝒪₂`. -/
theorem towerLeftToRight_app_towerFirstBaseHom (W : (polynomialTowerSite A B C)ᵒᵖ)
    (a : ULift.{u + 1} A) :
    (towerLeftToRight A B C).app W ((towerFirstBaseHom A B C).app W a) =
      (towerSecondBaseHom A B C).app W a := by
  refine ULift.ext _ _ ?_
  change (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj)
        ↑(towerRightAlgebra W.unop.unop.obj))
      (algebraMap A ↑(towerLeftAlgebra W.unop.unop.obj) a.down) =
    algebraMap A ↑(towerRightAlgebra W.unop.unop.obj) a.down
  exact (IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra W.unop.unop.obj)
    ↑(towerRightAlgebra W.unop.unop.obj) a.down).symm

/-- **The pushout square on sections.** The composite `P → Q → Q ⊗_P B` is the composite
`P → B → Q ⊗_P B`, so the image of `𝒪₁` in `𝒪₃` lies in the image of `B̲`. This is what makes
the composite of the two maps of the sequence of Tag 08QU vanish. -/
theorem towerRightToPushout_app_towerLeftToRight (W : (polynomialTowerSite A B C)ᵒᵖ)
    (p : (towerLeftRingPresheaf A B C).obj W) :
    (towerRightToPushout A B C).app W ((towerLeftToRight A B C).app W p) =
      (towerThirdBaseHom A B C).app W
        (ULift.up (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj) B p.down)) := by
  refine ULift.ext _ _ ?_
  change (1 : B) ⊗ₜ[↑(towerLeftAlgebra W.unop.unop.obj)]
      (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj)
        ↑(towerRightAlgebra W.unop.unop.obj) p.down) = _
  change _ = (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj) B p.down) ⊗ₜ
    (1 : ↑(towerRightAlgebra W.unop.unop.obj))
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
    (R := ↑(towerLeftAlgebra W.unop.unop.obj)) (A := B)
    (B := ↑(towerRightAlgebra W.unop.unop.obj)) p.down).symm

/-! ### Derivations transported along a map of presheaves of rings -/

section DerivationComp

open PresheafOfModules

variable {E : Type u₁} [Category.{v₁} E] {S₂ S₃ R₂ R₃ : Eᵒᵖ ⥤ CommRingCat.{w}}

/-- **A derivation transported along a map of presheaves of rings.** Let `κ : R₂ ⟶ R₃` be a map
of presheaves of commutative rings, let `D` be a derivation of `R₃` relative to `φ₃ : S₃ ⟶ R₃`
with values in a presheaf of `R₃`-modules `M₃`, let `M₂` be a presheaf of `R₂`-modules and let
`t` be a natural family of additive maps `M₃ ⟶ M₂` which is `κ`-semilinear. If the square
`σ, κ, φ₂, φ₃` commutes then `x ↦ t (D (κ x))` is a derivation of `R₂` relative to
`φ₂ : S₂ ⟶ R₂` with values in `M₂`. -/
def derivationComp (φ₂ : S₂ ⟶ R₂) {φ₃ : S₃ ⟶ R₃} (σ : S₂ ⟶ S₃) (κ : R₂ ⟶ R₃)
    (hσ : σ ≫ φ₃ = φ₂ ≫ κ)
    {M₃ : PresheafOfModules.{w} (R₃ ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    {M₂ : PresheafOfModules.{w} (R₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (D : M₃.Derivation' φ₃) (t : ∀ X, M₃.obj X →+ M₂.obj X)
    (ht_smul : ∀ (X : Eᵒᵖ) (r : R₂.obj X) (z : M₃.obj X),
      t X (κ.app X r • z) = r • t X z)
    (ht_nat : ∀ {X Y : Eᵒᵖ} (f : X ⟶ Y) (z : M₃.obj X),
      t Y (M₃.map f z) = M₂.map f (t X z)) :
    M₂.Derivation' φ₂ := by
  refine Derivation'.mk (fun X => ModuleCat.Derivation.mk
    (fun q => t X (D.d (κ.app X q))) (fun q q' => ?_) (fun q q' => ?_) (fun a => ?_))
    (fun {X Y} f x => ?_)
  · rw [map_add, map_add, map_add]
  · rw [map_mul, D.d_mul, map_add, ht_smul, ht_smul]
  · have h : κ.app X (φ₂.app X a) = φ₃.app X (σ.app X a) :=
      (congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) (NatTrans.congr_app hσ X)).symm.trans
        (by simp)
    rw [h, Derivation'.d_app, map_zero]
  · have h : κ.app Y ((R₂.map f) x) = (R₃.map f) (κ.app X x) :=
      congrArg (fun k : CommRingCat.Hom _ _ => k.hom x) (κ.naturality f)
    change t Y (D.d (κ.app Y ((R₂.map f) x))) = (M₂.map f) (t X (D.d (κ.app X x)))
    rw [h, D.d_map, ht_nat]

end DerivationComp

/-! ### The unit of the change-of-rings adjunction on sections -/

section ChangeOfRingsUnit

open PresheafOfModules Stacks.PresheafOfModules.ChangeOfRings

variable {E : Type u₁} [Category.{v₁} E] {O₁ O₂ : Eᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (G : PresheafOfModules.{w} (O₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- **The unit of the change-of-rings adjunction of Tag 03CU on sections**, as an additive map:
the map `z ↦ 1 ⊗ z` from the sections of a presheaf of `O₁`-modules `G` over `X` to the sections
of `O₂ ⊗_{O₁} G` over `X`. This is the natural `O₁`-semilinear family with which the two maps of
the sequence of Tag 08QU are built out of `CommAlgCat.derivationComp`. -/
def changeOfRingsUnit (X : Eᵒᵖ) : G.obj X →+ cofObj θ G X :=
  (unitApp θ (𝟙 ((changeOfRings θ).obj G)) X).hom.toAddMonoidHom

/-- The unit of the change-of-rings adjunction sends a section `z` to `1 ⊗ z`. -/
theorem changeOfRingsUnit_apply (X : Eᵒᵖ) (z : G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    changeOfRingsUnit θ G X z = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] z := by
  let := (θ.app X).hom.toAlgebra
  exact unitApp_apply θ (𝟙 ((changeOfRings θ).obj G)) X z

/-- The unit of the change-of-rings adjunction is `θ`-semilinear: `1 ⊗ (s • z) = θ(s) • (1 ⊗ z)`.
This is the hypothesis `ht_smul` of `CommAlgCat.derivationComp` for the two maps of Tag 08QU. -/
theorem changeOfRingsUnit_smul (X : Eᵒᵖ) (s : O₁.obj X) (z : G.obj X) :
    changeOfRingsUnit θ G X (s • z) = θ.app X s • changeOfRingsUnit θ G X z :=
  (unitApp θ (𝟙 ((changeOfRings θ).obj G)) X).hom.map_smul s z

/-- The unit of the change-of-rings adjunction is natural in the object of the site. This is the
hypothesis `ht_nat` of `CommAlgCat.derivationComp` for the two maps of Tag 08QU. -/
theorem changeOfRingsUnit_map {X Y : Eᵒᵖ} (f : X ⟶ Y) (z : G.obj X) :
    changeOfRingsUnit θ G Y (G.map f z) =
      (changeOfRingsObj θ G).map f (changeOfRingsUnit θ G X z) :=
  phi_naturality G ((restrictScalars θ).obj ((changeOfRings θ).obj G))
    (unitHom θ (𝟙 ((changeOfRings θ).obj G))) f z

/-- The counit-unit identity of the change-of-rings adjunction on sections: the map `O₂ ⊗ G ⟶ F`
attached to `φ : G ⟶ F` sends `1 ⊗ z` to `φ z`. -/
theorem counitHom_app_changeOfRingsUnit
    {F : PresheafOfModules.{w} (O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : G ⟶ (restrictScalars θ).obj F) (X : Eᵒᵖ) (z : G.obj X) :
    (counitHom θ φ).app X (changeOfRingsUnit θ G X z) = φ.app X z := by
  let := (θ.app X).hom.toAlgebra
  have h : changeOfRingsUnit θ G X z = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] z :=
    changeOfRingsUnit_apply θ G X z
  change (counitApp θ φ X).hom (changeOfRingsUnit θ G X z) = _
  rw [h, counitApp_tmul, one_smul]

/-- **A map out of a change of rings vanishes as soon as it kills the pure tensors `1 ⊗ z`.**
Indeed such a map corresponds under the adjunction of Tag 03CU to the map `z ↦ α (1 ⊗ z)`, and
the correspondence is a bijection. This is how the composite of the two maps of the sequence of
Tag 08QU is shown to vanish, without any induction on tensors. -/
theorem changeOfRingsHom_eq_zero
    {F : PresheafOfModules.{w} (O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (α : (changeOfRings θ).obj G ⟶ F)
    (h : ∀ (X : Eᵒᵖ) (z : G.obj X), α.app X (changeOfRingsUnit θ G X z) = 0) : α = 0 := by
  refine (homEquivCore θ G F).injective (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
  let := (θ.app X).hom.toAlgebra
  change (unitApp θ α X).hom z = (unitApp θ 0 X).hom z
  rw [unitApp_apply, unitApp_apply, ← changeOfRingsUnit_apply, h X z]
  simp only [PresheafOfModules.zero_app, ModuleCat.hom_zero]
  rfl

/-- A map `counitHom θ φ ≫ g` out of a change of rings vanishes as soon as `φ ≫ g` does. -/
private theorem counitHom_comp_eq_zero
    {F F' : PresheafOfModules.{w} (O₂ ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : G ⟶ (restrictScalars θ).obj F) (g : F ⟶ F')
    (h : φ ≫ (restrictScalars θ).map g = 0) : counitHom θ φ ≫ g = 0 := by
  refine changeOfRingsHom_eq_zero θ G _ fun X z => ?_
  change g.app X ((counitHom θ φ).app X (changeOfRingsUnit θ G X z)) = 0
  rw [counitHom_app_changeOfRingsUnit]
  exact congrArg (fun m => m.app X z) h

end ChangeOfRingsUnit

/-! ### The two maps of the sequence -/

section SequenceMaps

open PresheafOfModules PresheafOfModules.DifferentialsConstruction
open Stacks.PresheafOfModules.ChangeOfRings

/-- The map of constant sheaves of rings `g₁⁻¹A̲ ⟶ g₂⁻¹A̲` on `C_{C/B/A}`: both are the constant
sheaf with value `A`, and the map is the identity. It is the datum `σ` with which the derivation
giving the first map of the sequence is transported along `𝒪₁ ⟶ 𝒪₂`. -/
def towerFirstToSecondBase :
    (polynomialTowerFirst A B C).op ⋙ (polynomialBaseSheaf A (towerBaseAlgebra A B)).obj ⟶
      (polynomialTowerSecond A B C).op ⋙
        (polynomialBaseSheaf A (towerTotalAlgebra A C)).obj where
  app _ := CommRingCat.ofHom (RingHom.id (ULift.{u + 1} A))
  naturality _ _ _ := by simp [polynomialBaseSheaf]

/-- The map of constant sheaves of rings `g₂⁻¹A̲ ⟶ g₃⁻¹B̲` on `C_{C/B/A}`, the universe lift of
`A → B`. It is the datum `σ` with which the derivation giving the second map of the sequence is
transported along `𝒪₂ ⟶ 𝒪₃`. -/
def towerSecondToThirdBase :
    (polynomialTowerSecond A B C).op ⋙ (polynomialBaseSheaf A (towerTotalAlgebra A C)).obj ⟶
      (polynomialTowerThird A B C).op ⋙
        (polynomialBaseSheaf B (towerRelativeAlgebra B C)).obj where
  app _ := CommRingCat.ofHom (uliftRingHom (algebraMap A B))
  naturality _ _ _ := by simp [polynomialBaseSheaf]

/-- The square `A̲ ⟶ 𝒪₁ ⟶ 𝒪₂` against `A̲ ⟶ A̲ ⟶ 𝒪₂` commutes: on sections it is the identity
`A → P → Q` is `A → Q` of `CommAlgCat.towerLeftToRight_app_towerFirstBaseHom`. -/
theorem towerFirstBase_sq :
    towerFirstToSecondBase A B C ≫ towerSecondBaseHom A B C =
      towerFirstBaseHom A B C ≫ towerLeftToRight A B C := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  exact (towerLeftToRight_app_towerFirstBaseHom A B C W a).symm

/-- The square `A̲ ⟶ B̲ ⟶ 𝒪₃` against `A̲ ⟶ 𝒪₂ ⟶ 𝒪₃` commutes: on sections both composites are
`A → Q ⊗_P B`, because `1 ⊗ q` for `q` the image of `p` is the image of `p` under `P → B`. -/
theorem towerSecondBase_sq :
    towerSecondToThirdBase A B C ≫ towerThirdBaseHom A B C =
      towerSecondBaseHom A B C ≫ towerRightToPushout A B C := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  change (towerThirdBaseHom A B C).app W _ =
    (towerRightToPushout A B C).app W ((towerSecondBaseHom A B C).app W a)
  rw [← towerLeftToRight_app_towerFirstBaseHom A B C W a,
    towerRightToPushout_app_towerLeftToRight]
  refine congrArg _ (ULift.ext _ _ ?_)
  change algebraMap A B a.down =
    algebraMap ↑(towerLeftAlgebra W.unop.unop.obj) B
      (algebraMap A ↑(towerLeftAlgebra W.unop.unop.obj) a.down)
  exact IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra W.unop.unop.obj) B a.down

/-- **The derivation that gives the first map of the sequence of Tag 08QU.** It sends a section
`p` of `𝒪₁` to `1 ⊗ d(p)`, where `d` is the universal derivation of `g₂⁻¹Ω_{𝒪/A}` and `p` is
read in `𝒪₂` along `𝒪₁ ⟶ 𝒪₂`. Its target is `g₂⁻¹Ω₂` with its `𝒪₁`-module structure, obtained
by restricting scalars along `𝒪₁ ⟶ B̲ ⟶ C̲`. -/
def towerFirstDerivation :
    ((restrictScalars.{u + 1, u, u + 1, u + 1} (towerFirstAug A B C)).obj
        ((restrictScalars.{u + 1, u, u + 1, u + 1} (towerScalarHom A B C)).obj
          (towerSecondTerm A B C))).Derivation' (towerFirstBaseHom A B C) :=
  derivationComp (towerFirstBaseHom A B C) (towerFirstToSecondBase A B C)
    (towerLeftToRight A B C) (towerFirstBase_sq A B C)
    (φ₃ := towerSecondBaseHom A B C) (derivation' (towerSecondBaseHom A B C))
    (fun W => changeOfRingsUnit (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W)
    (fun W r z =>
      (changeOfRingsUnit_smul (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W
          ((towerLeftToRight A B C).app W r) z).trans
        (congrArg (fun c => c • changeOfRingsUnit (towerSecondAug A B C)
            (towerSecondOmegaPullback A B C) W z)
          (towerScalarHom_app_towerFirstAug A B C W r).symm))
    (fun f z => changeOfRingsUnit_map (towerSecondAug A B C)
      (towerSecondOmegaPullback A B C) f z)

/-- **The derivation that gives the second map of the sequence of Tag 08QU.** It sends a section
`q` of `𝒪₂` to `1 ⊗ d(1 ⊗ q)`, where `d` is the universal derivation of `g₃⁻¹Ω_{𝒪/B}` and
`1 ⊗ q` is the image of `q` in `𝒪₃ = Q ⊗_P B`. -/
def towerSecondDerivation :
    ((restrictScalars.{u + 1, u, u + 1, u + 1} (towerSecondAug A B C)).obj
        (towerThirdTerm A B C)).Derivation' (towerSecondBaseHom A B C) :=
  derivationComp (towerSecondBaseHom A B C) (towerSecondToThirdBase A B C)
    (towerRightToPushout A B C) (towerSecondBase_sq A B C)
    (φ₃ := towerThirdBaseHom A B C) (derivation' (towerThirdBaseHom A B C))
    (fun W => changeOfRingsUnit (towerThirdAug A B C) (towerThirdOmegaPullback A B C) W)
    (fun W r z =>
      (changeOfRingsUnit_smul (towerThirdAug A B C) (towerThirdOmegaPullback A B C) W
          ((towerRightToPushout A B C).app W r) z).trans
        (congrArg (fun c => c • changeOfRingsUnit (towerThirdAug A B C)
            (towerThirdOmegaPullback A B C) W z)
          (towerThirdAug_app_towerRightToPushout A B C W r)))
    (fun f z => changeOfRingsUnit_map (towerThirdAug A B C)
      (towerThirdOmegaPullback A B C) f z)

/-- **The first map `g₁⁻¹Ω₁ ⊗_{B̲} C̲ ⟶ g₂⁻¹Ω₂` of the sequence of Tag 08QU.** Both source and
target are base changes of presheaves of relative differentials, so by the change-of-rings
adjunction of Tag 03CU and the universal property of the presheaf of differentials the map is
the same datum as `CommAlgCat.towerFirstDerivation`, namely `c ⊗ b ⊗ d p ↦ c·b ⊗ d p`. -/
@[stacks 08QU "the first map g₁⁻¹Ω₁ ⊗_{B̲} C̲ ⟶ g₂⁻¹Ω₂ of the sequence"]
def towerFirstSequenceMap : towerFirstTerm A B C ⟶ towerSecondTerm A B C :=
  counitHom.{u + 1, u, u + 1, u + 1} (towerScalarHom A B C)
    (counitHom.{u + 1, u, u + 1, u + 1} (towerFirstAug A B C)
      ((isUniversal' (towerFirstBaseHom A B C)).desc (towerFirstDerivation A B C)))

/-- **The second map `g₂⁻¹Ω₂ ⟶ g₃⁻¹Ω₃` of the sequence of Tag 08QU**, the datum of
`CommAlgCat.towerSecondDerivation` under the change-of-rings adjunction of Tag 03CU and the
universal property of the presheaf of differentials: `c ⊗ d q ↦ c ⊗ d(1 ⊗ q)`. -/
@[stacks 08QU "the second map g₂⁻¹Ω₂ ⟶ g₃⁻¹Ω₃ of the sequence"]
def towerSecondSequenceMap : towerSecondTerm A B C ⟶ towerThirdTerm A B C :=
  counitHom.{u + 1, u, u + 1, u + 1} (towerSecondAug A B C)
    ((isUniversal' (towerSecondBaseHom A B C)).desc (towerSecondDerivation A B C))

/-- **The composite of the two maps of the sequence of Tag 08QU vanishes.** By the universal
properties the composite is the map attached to the derivation `p ↦ 1 ⊗ d(1 ⊗ image of p)` of
`𝒪₁` with values in `g₃⁻¹Ω₃`, and that derivation is zero: by the pushout square on sections
(`CommAlgCat.towerRightToPushout_app_towerLeftToRight`) the image of `p` in `𝒪₃` comes from
`B̲`, and `d` kills the image of the base sheaf of rings. -/
@[stacks 08QU "the two maps of the sequence compose to zero"]
theorem towerSequenceMap_comp :
    towerFirstSequenceMap A B C ≫ towerSecondSequenceMap A B C = 0 := by
  have h₃ : ((isUniversal' (towerFirstBaseHom A B C)).desc (towerFirstDerivation A B C)) ≫
      (restrictScalars.{u + 1, u, u + 1, u + 1} (towerFirstAug A B C)).map
        ((restrictScalars.{u + 1, u, u + 1, u + 1} (towerScalarHom A B C)).map
          (towerSecondSequenceMap A B C)) = 0 := by
    refine (isUniversal' (towerFirstBaseHom A B C)).postcomp_injective _ _ ?_
    ext W b
    have h1 : (((isUniversal' (towerFirstBaseHom A B C)).desc
          (towerFirstDerivation A B C)).app W) ((derivation' (towerFirstBaseHom A B C)).d b)
        = (towerFirstDerivation A B C).d b :=
      Derivation.congr_d ((isUniversal' (towerFirstBaseHom A B C)).fac
        (towerFirstDerivation A B C)) b
    have h2 : (towerFirstDerivation A B C).d b =
        changeOfRingsUnit (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W
          ((derivation' (towerSecondBaseHom A B C)).d ((towerLeftToRight A B C).app W b)) := rfl
    have h3 : (towerSecondSequenceMap A B C).app W
          (changeOfRingsUnit (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W
            ((derivation' (towerSecondBaseHom A B C)).d ((towerLeftToRight A B C).app W b)))
        = ((isUniversal' (towerSecondBaseHom A B C)).desc
            (towerSecondDerivation A B C)).app W
              ((derivation' (towerSecondBaseHom A B C)).d
                ((towerLeftToRight A B C).app W b)) :=
      counitHom_app_changeOfRingsUnit (towerSecondAug A B C)
        (towerSecondOmegaPullback A B C) _ W _
    have h4 : (((isUniversal' (towerSecondBaseHom A B C)).desc
          (towerSecondDerivation A B C)).app W)
            ((derivation' (towerSecondBaseHom A B C)).d ((towerLeftToRight A B C).app W b))
        = (towerSecondDerivation A B C).d ((towerLeftToRight A B C).app W b) :=
      Derivation.congr_d ((isUniversal' (towerSecondBaseHom A B C)).fac
        (towerSecondDerivation A B C)) _
    have h5 : (towerSecondDerivation A B C).d ((towerLeftToRight A B C).app W b) =
        changeOfRingsUnit (towerThirdAug A B C) (towerThirdOmegaPullback A B C) W
          ((derivation' (towerThirdBaseHom A B C)).d
            ((towerRightToPushout A B C).app W ((towerLeftToRight A B C).app W b))) := rfl
    have h6 : (derivation' (towerThirdBaseHom A B C)).d
          ((towerRightToPushout A B C).app W ((towerLeftToRight A B C).app W b)) = 0 := by
      rw [towerRightToPushout_app_towerLeftToRight]
      exact Derivation'.d_app _ _
    change (towerSecondSequenceMap A B C).app W
        ((((isUniversal' (towerFirstBaseHom A B C)).desc (towerFirstDerivation A B C)).app W)
          ((derivation' (towerFirstBaseHom A B C)).d b)) = 0
    rw [h1, h2, h3, h4, h5, h6, map_zero]
    rfl
  exact counitHom_comp_eq_zero _ _ _ _ (counitHom_comp_eq_zero _ _ _ _ h₃)

/-- **The sequence of Tag 08QU as a short complex of presheaves of `C̲`-modules on
`C_{C/B/A}`**, with the two maps above and the vanishing of their composite. -/
def towerShortComplexPresheaf :
    ShortComplex (PresheafOfModules.{u + 1} (towerConstantRingSheaf A B C).obj) :=
  ShortComplex.mk (towerFirstSequenceMap A B C) (towerSecondSequenceMap A B C)
    (towerSequenceMap_comp A B C)

/-- **The sequence of Tag 08QU as a short complex of sheaves of `C̲`-modules on `C_{C/B/A}`**,
the image of `CommAlgCat.towerShortComplexPresheaf` under the equivalence
`CommAlgCat.towerPresheafToSheaf`: every presheaf on the chaotic site is a sheaf. -/
@[stacks 08QU "the sequence 0 ⟶ g₁⁻¹Ω₁ ⊗_{B̲} C̲ ⟶ g₂⁻¹Ω₂ ⟶ g₃⁻¹Ω₃ ⟶ 0 of sheaves of \
  C̲-modules on C_{C/B/A}; its short exactness is not asserted here"]
def towerShortComplex : ShortComplex (SheafOfModules.{u + 1} (towerConstantRingSheaf A B C)) :=
  (towerShortComplexPresheaf A B C).map (towerPresheafToSheaf A B C)

end SequenceMaps

/-! ### Pointwise criteria for a map out of a base change -/

section BaseChangeExt

/-- **Two linear maps out of an extension of scalars agree as soon as they agree on the pure
tensors `1 ⊗ n`.** Every pure tensor of `S ⊗[R] N` is an `S`-multiple of one of those, and the
pure tensors generate. -/
theorem baseChange_linearMap_ext {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {N : Type*} [AddCommGroup N] [Module R N] {M : Type*} [AddCommGroup M] [Module S M]
    {φ ψ : (S ⊗[R] N) →ₗ[S] M} (h : ∀ n : N, φ ((1 : S) ⊗ₜ[R] n) = ψ ((1 : S) ⊗ₜ[R] n)) :
    φ = ψ := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s n =>
    have hs : s ⊗ₜ[R] n = s • ((1 : S) ⊗ₜ[R] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, h]

/-- **Two linear maps out of `S ⊗[R] Ω[R⁄R₀]` agree as soon as they agree on the elements
`1 ⊗ d r`.** The differentials `d r` span `Ω[R⁄R₀]` over `R`, and the `R`-action on
`S ⊗[R] Ω[R⁄R₀]` is the restriction of the `S`-action. -/
theorem baseChange_kaehler_ext {R₀ R S : Type*} [CommRing R₀] [CommRing R] [CommRing S]
    [Algebra R₀ R] [Algebra R S] {M : Type*} [AddCommGroup M] [Module S M]
    {φ ψ : (S ⊗[R] Ω[R⁄R₀]) →ₗ[S] M}
    (h : ∀ r : R, φ ((1 : S) ⊗ₜ[R] KaehlerDifferential.D R₀ R r) =
      ψ ((1 : S) ⊗ₜ[R] KaehlerDifferential.D R₀ R r)) :
    φ = ψ := by
  refine baseChange_linearMap_ext fun n => ?_
  have hmem : n ∈ (⊤ : Submodule R Ω[R⁄R₀]) := trivial
  rw [← KaehlerDifferential.span_range_derivation] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    exact h r
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul S a, map_smul, map_smul, hx]

/-- **Two linear maps out of `S ⊗[A₀] (A₀ ⊗[R] Ω[R⁄R₀])` agree as soon as they agree on the
elements `1 ⊗ 1 ⊗ d r`.** This is `CommAlgCat.baseChange_kaehler_ext` for a tower of two base
changes; it is the criterion by which the first square of the identification of the sequence of
Tag 08QU with the objectwise split sequence is checked. -/
theorem doubleBaseChange_kaehler_ext {R₀ R A₀ S : Type*} [CommRing R₀] [CommRing R]
    [CommRing A₀] [CommRing S] [Algebra R₀ R] [Algebra R A₀] [Algebra A₀ S] [Algebra R S]
    [IsScalarTower R A₀ S] {M : Type*} [AddCommGroup M] [Module S M]
    {φ ψ : (S ⊗[A₀] (A₀ ⊗[R] Ω[R⁄R₀])) →ₗ[S] M}
    (h : ∀ r : R, φ ((1 : S) ⊗ₜ[A₀] ((1 : A₀) ⊗ₜ[R] KaehlerDifferential.D R₀ R r)) =
      ψ ((1 : S) ⊗ₜ[A₀] ((1 : A₀) ⊗ₜ[R] KaehlerDifferential.D R₀ R r))) :
    φ = ψ := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R A₀ S S Ω[R⁄R₀]
  have := baseChange_kaehler_ext (R₀ := R₀) (R := R) (S := S)
    (φ := φ ∘ₗ e.symm.toLinearMap) (ψ := ψ ∘ₗ e.symm.toLinearMap) fun r => by simpa [e] using h r
  exact LinearMap.ext fun x => by simpa using LinearMap.congr_fun this (e x)

end BaseChangeExt

/-- **The sequence of Tag 08QU is short exact as soon as it is short exact at every object of
`C_{C/B/A}`.** This is the reduction of the exactness asserted by the tag to the statement of
`CommAlgCat.towerDifferential_shortExact_extendScalars` over a polynomial tower: presheaves of
`C̲`-modules are short exact objectwise, and `CommAlgCat.towerPresheafToSheaf` is an additive
equivalence, hence exact. -/
theorem towerShortComplex_shortExact_of_objectwise
    (h : ∀ W, ((towerShortComplexPresheaf A B C).map
      (PresheafOfModules.evaluation (towerConstantRingSheaf A B C).obj W)).ShortExact) :
    (towerShortComplex A B C).ShortExact :=
  (PresheafOfModules.shortExact_of_objectwise _ h).map_of_exact (towerPresheafToSheaf A B C)

/-! ### The short exactness of the sequence -/

section Exactness

open PresheafOfModules PresheafOfModules.DifferentialsConstruction
open Stacks.PresheafOfModules.ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The sequence of Tag 08QU is short exact over every object of `C_{C/B/A}`.** Over the
polynomial tower `(P → B, Q → C)`, with `T = Q ⊗_P B` and every ring replaced by its universe
lift, the three modules of sections are `C̲(W) ⊗_{B̲(W)} (B̲(W) ⊗_P Ω_{P/A})`, `C̲(W) ⊗_Q Ω_{Q/A}`
and `C̲(W) ⊗_T Ω_{T/B}`, and the sequence they form is the split sequence of
`CommAlgCat.towerDifferential_shortExact_extendScalars` for the tower `A → P → Q` base changed
along the augmentation `Q → C̲(W)`. The middle terms agree on the nose
(`CommAlgCat.towerSecondTerm_obj`); the first terms are identified by cancelling the base change
twice through `C̲(W) ⊗_P Ω_{P/A}`, and the third ones by
`KaehlerDifferential.tensorKaehlerEquiv`, available because
`CommAlgCat.towerSections_isPushout` makes `T` the pushout of `B ← P → Q`. Both squares are
checked on the generators `1 ⊗ 1 ⊗ d p` and `1 ⊗ d q`, where the two maps of the sequence are
computed by the change-of-rings adjunction of Tag 03CU. -/
@[stacks 08QU "the sequence of sections over a polynomial tower is short exact: the objectwise \
  form of the short exactness"]
theorem towerShortComplexPresheaf_shortExact_obj (W : (polynomialTowerSite A B C)ᵒᵖ) :
    ((towerShortComplexPresheaf A B C).map
      (PresheafOfModules.evaluation (towerConstantRingSheaf A B C).obj W)).ShortExact := by
  let iAP : Algebra (ULift.{u + 1} A) ((towerLeftRingPresheaf A B C).obj W) :=
    ((towerFirstBaseHom A B C).app W).hom.toAlgebra
  let iAQ : Algebra (ULift.{u + 1} A) ((towerRightRingPresheaf A B C).obj W) :=
    ((towerSecondBaseHom A B C).app W).hom.toAlgebra
  let iPQ : Algebra ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) :=
    ((towerLeftToRight A B C).app W).hom.toAlgebra
  let iPB : Algebra ((towerLeftRingPresheaf A B C).obj W)
      ((towerBaseConstantPresheaf A B C).obj W) :=
    ((towerFirstAug A B C).app W).hom.toAlgebra
  let iBC : Algebra ((towerBaseConstantPresheaf A B C).obj W)
      ((towerConstantSheaf A B C).obj.obj W) :=
    ((towerScalarHom A B C).app W).hom.toAlgebra
  let iQC : Algebra ((towerRightRingPresheaf A B C).obj W)
      ((towerConstantSheaf A B C).obj.obj W) :=
    ((towerSecondAug A B C).app W).hom.toAlgebra
  let iTC : Algebra ((towerPushoutRingPresheaf A B C).obj W)
      ((towerConstantSheaf A B C).obj.obj W) :=
    ((towerThirdAug A B C).app W).hom.toAlgebra
  let iQT : Algebra ((towerRightRingPresheaf A B C).obj W)
      ((towerPushoutRingPresheaf A B C).obj W) :=
    ((towerRightToPushout A B C).app W).hom.toAlgebra
  let iBT : Algebra (ULift.{u + 1} B) ((towerPushoutRingPresheaf A B C).obj W) :=
    ((towerThirdBaseHom A B C).app W).hom.toAlgebra
  let iPC : Algebra ((towerLeftRingPresheaf A B C).obj W)
      ((towerConstantSheaf A B C).obj.obj W) :=
    ((towerFirstAug A B C).app W ≫ (towerScalarHom A B C).app W).hom.toAlgebra
  let iPT : Algebra ((towerLeftRingPresheaf A B C).obj W)
      ((towerPushoutRingPresheaf A B C).obj W) :=
    ((towerLeftToRight A B C).app W ≫ (towerRightToPushout A B C).app W).hom.toAlgebra
  let iPB' : Algebra ((towerLeftRingPresheaf A B C).obj W) (ULift.{u + 1} B) :=
    (uliftRingHom (algebraMap ↑(towerLeftAlgebra W.unop.unop.obj) B)).toAlgebra
  -- the same two algebra structures, in the spelling the change-of-rings lemmas produce
  let iPBn : Algebra ((towerLeftRingPresheaf A B C).obj W)
      ((polynomialConstantSheaf A (towerBaseAlgebra A B)).obj.obj
        ((polynomialTowerFirst A B C).op.obj W)) := iPB
  let iQCn : Algebra ((towerRightRingPresheaf A B C).obj W)
      ((polynomialConstantSheaf A (towerTotalAlgebra A C)).obj.obj
        ((polynomialTowerSecond A B C).op.obj W)) := iQC
  -- the five scalar towers on sections
  have tPBC : IsScalarTower ((towerLeftRingPresheaf A B C).obj W)
      ((towerBaseConstantPresheaf A B C).obj W) ((towerConstantSheaf A B C).obj.obj W) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have tPQC : IsScalarTower ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) ((towerConstantSheaf A B C).obj.obj W) :=
    IsScalarTower.of_algebraMap_eq fun p => towerScalarHom_app_towerFirstAug A B C W p
  have tQTC : IsScalarTower ((towerRightRingPresheaf A B C).obj W)
      ((towerPushoutRingPresheaf A B C).obj W) ((towerConstantSheaf A B C).obj.obj W) :=
    IsScalarTower.of_algebraMap_eq fun q =>
      (towerThirdAug_app_towerRightToPushout A B C W q).symm
  have tPQT : IsScalarTower ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) ((towerPushoutRingPresheaf A B C).obj W) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have tPBT : IsScalarTower ((towerLeftRingPresheaf A B C).obj W) (ULift.{u + 1} B)
      ((towerPushoutRingPresheaf A B C).obj W) :=
    IsScalarTower.of_algebraMap_eq fun p =>
      towerRightToPushout_app_towerLeftToRight A B C W p
  have tAPQ : IsScalarTower (ULift.{u + 1} A) ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (towerLeftToRight_app_towerFirstBaseHom A B C W a).symm
  -- the pushout square, for these algebra structures
  have hpush : Algebra.IsPushout ((towerLeftRingPresheaf A B C).obj W) (ULift.{u + 1} B)
      ((towerRightRingPresheaf A B C).obj W) ((towerPushoutRingPresheaf A B C).obj W) :=
    Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout)
      (Algebra.uliftTensorProductEquiv'.{u, u + 1} (iAT := iBT)
        ↑(towerLeftAlgebra W.unop.unop.obj) B ↑(towerRightAlgebra W.unop.unop.obj)
        (fun _ => rfl))
      (RingHom.ext fun _ => rfl)
  have hsm : Algebra.FormallySmooth ((towerLeftRingPresheaf A B C).obj W)
      ((towerRightRingPresheaf A B C).obj W) := towerSections_formallySmooth A B C W
  have htarget := towerDifferential_shortExact_extendScalars.{u + 1} (ULift.{u + 1} A)
    ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
    ((towerConstantSheaf A B C).obj.obj W) ((towerSecondAug A B C).app W).hom
  -- the first map of the sequence on the generators `1 ⊗ 1 ⊗ d p`
  have hfours : ∀ p : ((towerLeftRingPresheaf A B C).obj W),
      (towerFirstSequenceMap A B C).app W
          ((1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerBaseConstantPresheaf A B C).obj W)]
              ((1 : ((towerBaseConstantPresheaf A B C).obj W))
                ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                  (KaehlerDifferential.D (ULift.{u + 1} A)
                    ((towerLeftRingPresheaf A B C).obj W) p)))
        = (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D (ULift.{u + 1} A)
                ((towerRightRingPresheaf A B C).obj W)
                (algebraMap ((towerLeftRingPresheaf A B C).obj W)
                  ((towerRightRingPresheaf A B C).obj W) p)) := by
    intro p
    refine Eq.trans (congrArg ((towerFirstSequenceMap A B C).app W)
      (?_ : ((1 : ((towerConstantSheaf A B C).obj.obj W))
          ⊗ₜ[((towerBaseConstantPresheaf A B C).obj W)]
            ((1 : ((towerBaseConstantPresheaf A B C).obj W))
              ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                (KaehlerDifferential.D (ULift.{u + 1} A)
                  ((towerLeftRingPresheaf A B C).obj W) p)))
        = changeOfRingsUnit (towerScalarHom A B C) (towerFirstPullback A B C) W
            (changeOfRingsUnit (towerFirstAug A B C) (towerFirstOmegaPullback A B C) W
              ((derivation' (towerFirstBaseHom A B C)).d p)))) ?_
    · exact ((changeOfRingsUnit_apply (towerScalarHom A B C) (towerFirstPullback A B C) W
        (changeOfRingsUnit (towerFirstAug A B C) (towerFirstOmegaPullback A B C) W
          ((derivation' (towerFirstBaseHom A B C)).d p))).trans
        (congrArg (fun y => (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerBaseConstantPresheaf A B C).obj W)] y)
          (changeOfRingsUnit_apply (towerFirstAug A B C) (towerFirstOmegaPullback A B C) W
            ((derivation' (towerFirstBaseHom A B C)).d p)))).symm
    · refine Eq.trans (counitHom_app_changeOfRingsUnit (towerScalarHom A B C)
        (towerFirstPullback A B C) _ W _) ?_
      refine Eq.trans (counitHom_app_changeOfRingsUnit (towerFirstAug A B C)
        (towerFirstOmegaPullback A B C) _ W _) ?_
      refine Eq.trans (Derivation.congr_d
        ((isUniversal' (towerFirstBaseHom A B C)).fac (towerFirstDerivation A B C)) p) ?_
      exact changeOfRingsUnit_apply (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W _
  -- the second map of the sequence on the generators `1 ⊗ d q`
  have hgours : ∀ q : ((towerRightRingPresheaf A B C).obj W),
      (towerSecondSequenceMap A B C).app W
          ((1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D (ULift.{u + 1} A)
                ((towerRightRingPresheaf A B C).obj W) q))
        = (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerPushoutRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D (ULift.{u + 1} B)
                ((towerPushoutRingPresheaf A B C).obj W)
                (algebraMap ((towerRightRingPresheaf A B C).obj W)
                  ((towerPushoutRingPresheaf A B C).obj W) q)) := by
    intro q
    refine Eq.trans (congrArg ((towerSecondSequenceMap A B C).app W)
      (?_ : ((1 : ((towerConstantSheaf A B C).obj.obj W))
          ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
            (KaehlerDifferential.D (ULift.{u + 1} A)
              ((towerRightRingPresheaf A B C).obj W) q))
        = changeOfRingsUnit (towerSecondAug A B C) (towerSecondOmegaPullback A B C) W
            ((derivation' (towerSecondBaseHom A B C)).d q))) ?_
    · exact (changeOfRingsUnit_apply (towerSecondAug A B C)
        (towerSecondOmegaPullback A B C) W _).symm
    · refine Eq.trans (counitHom_app_changeOfRingsUnit (towerSecondAug A B C)
        (towerSecondOmegaPullback A B C) _ W _) ?_
      refine Eq.trans (Derivation.congr_d
        ((isUniversal' (towerSecondBaseHom A B C)).fac (towerSecondDerivation A B C)) q) ?_
      exact changeOfRingsUnit_apply (towerThirdAug A B C) (towerThirdOmegaPullback A B C) W _
  refine ShortComplex.shortExact_of_iso (Iso.symm ?_) htarget
  refine ShortComplex.isoMk
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
          ((towerLeftRingPresheaf A B C).obj W) ((towerBaseConstantPresheaf A B C).obj W)
          ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
          Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]) ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
          ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
          Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]).symm).toModuleIso
    (Iso.refl _)
    ((TensorProduct.AlgebraTensorModule.congr
          (LinearEquiv.refl ((towerConstantSheaf A B C).obj.obj W)
            ((towerConstantSheaf A B C).obj.obj W))
          (KaehlerDifferential.tensorKaehlerEquiv ((towerLeftRingPresheaf A B C).obj W)
            (ULift.{u + 1} B) ((towerRightRingPresheaf A B C).obj W)
            ((towerPushoutRingPresheaf A B C).obj W)).symm) ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          ((towerRightRingPresheaf A B C).obj W) ((towerPushoutRingPresheaf A B C).obj W)
          ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
          Ω[((towerRightRingPresheaf A B C).obj W)⁄
            ((towerLeftRingPresheaf A B C).obj W)])).toModuleIso ?_ ?_
  · simp only [Iso.refl_hom]
    refine ModuleCat.hom_ext (doubleBaseChange_kaehler_ext
      (R₀ := (ULift.{u + 1} A)) (R := ((towerLeftRingPresheaf A B C).obj W))
      (A₀ := ((towerBaseConstantPresheaf A B C).obj W))
      (S := ((towerConstantSheaf A B C).obj.obj W)) (fun p => ?_))
    have t1 : ((TensorProduct.AlgebraTensorModule.cancelBaseChange
            ((towerLeftRingPresheaf A B C).obj W) ((towerBaseConstantPresheaf A B C).obj W)
            ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
            Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]) ≪≫ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
            ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
            Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]).symm)
          ((1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerBaseConstantPresheaf A B C).obj W)]
              ((1 : ((towerBaseConstantPresheaf A B C).obj W))
                ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                  (KaehlerDifferential.D (ULift.{u + 1} A)
                    ((towerLeftRingPresheaf A B C).obj W) p)))
        = (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              ((1 : ((towerRightRingPresheaf A B C).obj W))
                ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                  (KaehlerDifferential.D (ULift.{u + 1} A)
                    ((towerLeftRingPresheaf A B C).obj W) p)) := by
      rw [LinearEquiv.trans_apply,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    change (ModuleCat.Hom.hom
        ((ModuleCat.extendScalars ((towerSecondAug A B C).app W).hom).map
          (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange (ULift.{u + 1} A)
            ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)))))
        (((TensorProduct.AlgebraTensorModule.cancelBaseChange
              ((towerLeftRingPresheaf A B C).obj W) ((towerBaseConstantPresheaf A B C).obj W)
              ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
              Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]) ≪≫ₗ
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
              ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
              Ω[((towerLeftRingPresheaf A B C).obj W)⁄(ULift.{u + 1} A)]).symm)
          ((1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerBaseConstantPresheaf A B C).obj W)]
              ((1 : ((towerBaseConstantPresheaf A B C).obj W))
                ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                  (KaehlerDifferential.D (ULift.{u + 1} A)
                    ((towerLeftRingPresheaf A B C).obj W) p)))) = _
    rw [t1]
    change (1 : ((towerConstantSheaf A B C).obj.obj W))
        ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
          (KaehlerDifferential.mapBaseChange (ULift.{u + 1} A)
            ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
            ((1 : ((towerRightRingPresheaf A B C).obj W))
              ⊗ₜ[((towerLeftRingPresheaf A B C).obj W)]
                (KaehlerDifferential.D (ULift.{u + 1} A)
                  ((towerLeftRingPresheaf A B C).obj W) p))) = _
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    exact (hfours p).symm
  · simp only [Iso.refl_hom]
    refine ModuleCat.hom_ext (baseChange_kaehler_ext
      (R₀ := (ULift.{u + 1} A)) (R := ((towerRightRingPresheaf A B C).obj W))
      (S := ((towerConstantSheaf A B C).obj.obj W)) (fun q => ?_))
    have hsymm : (KaehlerDifferential.tensorKaehlerEquiv
            ((towerLeftRingPresheaf A B C).obj W) (ULift.{u + 1} B)
            ((towerRightRingPresheaf A B C).obj W)
            ((towerPushoutRingPresheaf A B C).obj W)).symm
          (KaehlerDifferential.D (ULift.{u + 1} B)
            ((towerPushoutRingPresheaf A B C).obj W)
            (algebraMap ((towerRightRingPresheaf A B C).obj W)
              ((towerPushoutRingPresheaf A B C).obj W) q))
        = (1 : ((towerPushoutRingPresheaf A B C).obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D ((towerLeftRingPresheaf A B C).obj W)
                ((towerRightRingPresheaf A B C).obj W) q) := by
      rw [LinearEquiv.symm_apply_eq, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]
    have hE3 : ((TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl ((towerConstantSheaf A B C).obj.obj W)
              ((towerConstantSheaf A B C).obj.obj W))
            (KaehlerDifferential.tensorKaehlerEquiv ((towerLeftRingPresheaf A B C).obj W)
              (ULift.{u + 1} B) ((towerRightRingPresheaf A B C).obj W)
              ((towerPushoutRingPresheaf A B C).obj W)).symm) ≪≫ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            ((towerRightRingPresheaf A B C).obj W) ((towerPushoutRingPresheaf A B C).obj W)
            ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
            Ω[((towerRightRingPresheaf A B C).obj W)⁄
              ((towerLeftRingPresheaf A B C).obj W)]))
          ((1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerPushoutRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D (ULift.{u + 1} B)
                ((towerPushoutRingPresheaf A B C).obj W)
                (algebraMap ((towerRightRingPresheaf A B C).obj W)
                  ((towerPushoutRingPresheaf A B C).obj W) q)))
        = (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D ((towerLeftRingPresheaf A B C).obj W)
                ((towerRightRingPresheaf A B C).obj W) q) := by
      rw [LinearEquiv.trans_apply,
        show (TensorProduct.AlgebraTensorModule.congr
              (LinearEquiv.refl ((towerConstantSheaf A B C).obj.obj W)
                ((towerConstantSheaf A B C).obj.obj W))
              (KaehlerDifferential.tensorKaehlerEquiv ((towerLeftRingPresheaf A B C).obj W)
                (ULift.{u + 1} B) ((towerRightRingPresheaf A B C).obj W)
                ((towerPushoutRingPresheaf A B C).obj W)).symm)
            ((1 : ((towerConstantSheaf A B C).obj.obj W))
              ⊗ₜ[((towerPushoutRingPresheaf A B C).obj W)]
                (KaehlerDifferential.D (ULift.{u + 1} B)
                  ((towerPushoutRingPresheaf A B C).obj W)
                  (algebraMap ((towerRightRingPresheaf A B C).obj W)
                    ((towerPushoutRingPresheaf A B C).obj W) q)))
          = (1 : ((towerConstantSheaf A B C).obj.obj W))
              ⊗ₜ[((towerPushoutRingPresheaf A B C).obj W)]
                ((KaehlerDifferential.tensorKaehlerEquiv
                    ((towerLeftRingPresheaf A B C).obj W) (ULift.{u + 1} B)
                    ((towerRightRingPresheaf A B C).obj W)
                    ((towerPushoutRingPresheaf A B C).obj W)).symm
                  (KaehlerDifferential.D (ULift.{u + 1} B)
                    ((towerPushoutRingPresheaf A B C).obj W)
                    (algebraMap ((towerRightRingPresheaf A B C).obj W)
                      ((towerPushoutRingPresheaf A B C).obj W) q))) from rfl,
        hsymm, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have hLHS : (1 : ((towerConstantSheaf A B C).obj.obj W))
          ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
            (KaehlerDifferential.map (ULift.{u + 1} A)
              ((towerLeftRingPresheaf A B C).obj W) ((towerRightRingPresheaf A B C).obj W)
              ((towerRightRingPresheaf A B C).obj W)
              (KaehlerDifferential.D (ULift.{u + 1} A)
                ((towerRightRingPresheaf A B C).obj W) q))
        = (1 : ((towerConstantSheaf A B C).obj.obj W))
            ⊗ₜ[((towerRightRingPresheaf A B C).obj W)]
              (KaehlerDifferential.D ((towerLeftRingPresheaf A B C).obj W)
                ((towerRightRingPresheaf A B C).obj W) q) := by
      rw [KaehlerDifferential.map_D, Algebra.algebraMap_self_apply]
    exact Eq.trans hLHS
      ((congrArg (fun y => ((TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl ((towerConstantSheaf A B C).obj.obj W)
              ((towerConstantSheaf A B C).obj.obj W))
            (KaehlerDifferential.tensorKaehlerEquiv ((towerLeftRingPresheaf A B C).obj W)
              (ULift.{u + 1} B) ((towerRightRingPresheaf A B C).obj W)
              ((towerPushoutRingPresheaf A B C).obj W)).symm) ≪≫ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            ((towerRightRingPresheaf A B C).obj W) ((towerPushoutRingPresheaf A B C).obj W)
            ((towerConstantSheaf A B C).obj.obj W) ((towerConstantSheaf A B C).obj.obj W)
            Ω[((towerRightRingPresheaf A B C).obj W)⁄
              ((towerLeftRingPresheaf A B C).obj W)])) y) (hgours q)).trans hE3).symm

/-- **Tag 08QU: the sequence of sheaves of `C̲`-modules on `C_{C/B/A}`
`0 → g₁⁻¹Ω₁ ⊗_{B̲} C̲ → g₂⁻¹Ω₂ → g₃⁻¹Ω₃ → 0` is short exact.** By
`CommAlgCat.towerShortComplex_shortExact_of_objectwise` this is the objectwise statement
`CommAlgCat.towerShortComplexPresheaf_shortExact_obj`: a short complex of presheaves of
`C̲`-modules on the chaotic site `C_{C/B/A}` is short exact as soon as its sequence of sections
over every polynomial tower is, and there the sequence is the split differential sequence of
Algebra, Lemma 10.138.9 for `A → P → Q` base changed along the augmentation `Q → C̲`. -/
@[stacks 08QU "the sequence of sheaves of C-modules on C_{C/B/A} is short exact"]
theorem towerShortComplex_shortExact : (towerShortComplex A B C).ShortExact :=
  towerShortComplex_shortExact_of_objectwise A B C
    (towerShortComplexPresheaf_shortExact_obj A B C)

end Exactness

end CommAlgCat

end
