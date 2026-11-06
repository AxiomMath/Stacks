module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation

/-!
# Checking a dualizing complex on one affine open cover

On a locally Noetherian scheme `X` an object `K` of `D(𝒪_X)` is a dualizing complex when over
every affine open `U` it is the associated sheaf of a dualizing complex over `Γ(X, U)`, the
predicate `Stacks.Duality.HasDualizingModelOn`. [Stacks, Tag 0A86] says that this all-affine-open
condition is equivalent to the same condition read on the members of a single affine open cover.

One implication is immediate: the affine opens of `X` already cover it. The other is an
affine-communication argument. Carrying a dualizing model is a property of affine opens, and by
`AlgebraicGeometry.of_affine_open_cover` such a property holds at every affine open as soon as it
holds on one affine open cover, passes to the basic opens of sections, and descends from a family
of basic opens whose sections generate the unit ideal. That lemma packages [Stacks, Tag 01IW],
the existence of a common standard open of two affine opens, with the quasi-compactness of an
affine open, which is exactly the geometric input of the proof of [Stacks, Tag 0A86].

The two remaining steps of that argument are the hypotheses of
`Stacks.Duality.isDualizingComplex_of_affineOpenCover`: localising a dualizing complex to a basic
open keeps it dualizing ([Stacks, Tag 0A7G]), and a complex whose localisations at a family
generating the unit ideal are dualizing is dualizing ([Stacks, Tag 0A7H]). Both are available
over a ring; transporting them across the affine dictionary of
`Stacks.AffineTilde.tildeRestrictIso` is what the hypotheses still ask for.

## Main definitions

* `Stacks.AffineTilde.tildeRestrictDerivedIso` — the affine dictionary on unbounded derived
  categories: along a ring map whose spectrum is an open immersion and whose extension of scalars
  is exact, restricting `M^~` is `(S ⊗ᴸ_R M)^~`.

## Main results

* `Stacks.Duality.exists_affineOpenCover_hasDualizingModelOn` — the implication (1) ⟹ (2) of
  [Stacks, Tag 0A86].
* `Stacks.Duality.isDualizingComplex_of_affineOpenCover` — the implication (2) ⟹ (1) of
  [Stacks, Tag 0A86], from the basic-open and unit-ideal steps of its proof.

## Implementation notes

No `@[stacks 0A86]` attribute appears below. The content of the tag is the equivalence, and the
reverse implication is proved here only relative to its two ring-theoretic steps, which are
hypotheses of `Stacks.Duality.isDualizingComplex_of_affineOpenCover` rather than theorems; the
audit scanner keys on the bare four-character tag, so an attribute on a conditional form would
render 0A86 formalized. The attribute belongs on the unconditional statement once the two steps
land.

`AlgebraicGeometry.of_affine_open_cover` is stated for a predicate on `X.affineOpens`, whose
basic opens are spelled `AlgebraicGeometry.Scheme.affineBasicOpen`; the hypotheses below are
phrased in that vocabulary so that no conversion is needed at the point of use.

The derived categories of `Stacks.Duality.HasDualizingModelOn` that depend on the affine open are
sealed inside its body at `CategoryTheory.HasDerivedCategory.standard`, so this file installs
that model with priority `10000`, as
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` requires of its
importers: the import closure carries global `HasDerivedCategory` instances for the locally small
model, which beat a default-priority local attribute.

## References

* [Stacks Project, Tag 01IW](https://stacks.math.columbia.edu/tag/01IW)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AffineTilde

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
  [PreservesFiniteLimits (ModuleCat.extendScalars φ.hom)]

/-- **The affine dictionary on unbounded derived categories.** For a ring map `φ : R ⟶ S` whose
spectrum is an open immersion and along which extension of scalars is exact, restricting the
complex of sheaves `M^~` associated to an object of `D(R)` along `Spec φ` gives the complex of
sheaves associated to `S ⊗ᴸ_R M` in `D(S)`.

This is `Stacks.AffineTilde.tildeRestrictIso` carried through `Functor.mapDerivedCategory`. -/
def tildeRestrictDerivedIso :
    (tilde.functor R).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor (Spec.map φ)).mapDerivedCategory ≅
      (ModuleCat.extendScalars φ.hom).mapDerivedCategory ⋙
        (tilde.functor S).mapDerivedCategory :=
  letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor (Spec.map φ)) :=
    Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor _
  letI : PreservesFiniteColimits (Scheme.Modules.restrictFunctor (Spec.map φ)) := inferInstance
  Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (tildeRestrictIso φ) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _)).symm

end Stacks.AffineTilde

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- A dualizing complex on a locally Noetherian scheme carries a dualizing model at every member
of the covering of `X` by all of its affine opens.

This is the implication (1) ⟹ (2) of [Stacks, Tag 0A86], which holds because the condition of
(1) is the condition of (2) read at every affine open. -/
theorem exists_affineOpenCover_hasDualizingModelOn {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    ∃ (ι : Type u) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)),
      ⨆ i, U i = ⊤ ∧ ∀ i, HasDualizingModelOn K (U i) (hU i) :=
  ⟨X.affineOpens, fun V => V.1, fun V => V.2, iSup_affineOpens_eq_top X, fun V => hK V.1 V.2⟩

/-- **The affine-communication reduction of [Stacks, Tag 0A86].** If carrying a dualizing model
passes from an affine open to the basic opens of its sections, and descends from a family of
basic opens whose sections generate the unit ideal, then a dualizing model on one affine open
cover gives one on every affine open.

The two hypotheses are exactly the two steps of the proof of [Stacks, Tag 0A86]: the first is
[Stacks, Tag 0A7G] carried through the affine dictionary, and the second is
[Stacks, Tag 0A7H]. The passage from them to all affine opens is the affine communication
lemma, which packages [Stacks, Tag 01IW] with the quasi-compactness of an affine open. -/
theorem isDualizingComplex_of_affineOpenCover {K : DerivedCategory X.Modules}
    (hbasicOpen : ∀ (V : X.affineOpens) (f : Γ(X, V.1)),
      HasDualizingModelOn K V.1 V.2 →
        HasDualizingModelOn K (X.affineBasicOpen f).1 (X.affineBasicOpen f).2)
    (hspan : ∀ (V : X.affineOpens) (s : Finset Γ(X, V.1)),
      Ideal.span (s : Set Γ(X, V.1)) = ⊤ →
        (∀ f : s, HasDualizingModelOn K (X.affineBasicOpen f.1).1
          (X.affineBasicOpen f.1).2) → HasDualizingModelOn K V.1 V.2)
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i, HasDualizingModelOn K (U i) (hU i)) :
    IsDualizingComplex K := fun V hV =>
  of_affine_open_cover (P := fun W => HasDualizingModelOn K W.1 W.2)
    (fun i => ⟨U i, hU i⟩) (by simpa using hcov) ⟨V, hV⟩
    (fun W f hW => hbasicOpen W f hW) (fun W s hs hW => hspan W s hs hW) h

end Stacks.Duality

end
