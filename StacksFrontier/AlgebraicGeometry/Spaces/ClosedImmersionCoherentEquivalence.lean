module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType

/-!
# Coherent modules on a closed subspace of a locally Noetherian algebraic space

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian algebraic spaces over a scheme `S`
contained in a big fppf site `B`, and let `ℐ = ker(i♯) ⊆ 𝒪_X` be the quasi-coherent sheaf of
ideals cutting out `Z`.  **Stacks 08AM** asserts that direct image along `i` induces an
equivalence between the category of coherent `𝒪_Z`-modules and the category of coherent
`𝒪_X`-modules annihilated by `ℐ`.  This file proves it.

The source's direction is the one realized here: `i_*` goes *from* the coherent `𝒪_Z`-modules
*to* the coherent `𝒪_X`-modules annihilated by `ℐ`, and the equivalence
`AlgebraicGeometry.Space.pushforwardCoherentEquivalence` has
`AlgebraicGeometry.Space.pushforwardCoherent` for its functor — which composed with the
inclusion of the full subcategory *is* `AlgebraicGeometry.Space.modulePushforward`, by
`AlgebraicGeometry.Space.pushforwardCoherentCompIso`, so the equivalence is `i_*` and not an
abstract replacement for it.

## Main definitions

* `AlgebraicGeometry.Space.coherentAnnihilatedByKerIdeal`: the coherent `𝒪_X`-modules
  annihilated by `ℐ`, as a property of objects of the category of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.pushforwardCoherent`: direct image as a functor
  `Coh(𝒪_Z) ⥤ {ℱ ∈ Coh(𝒪_X) | ℐℱ = 0}`.
* `AlgebraicGeometry.Space.pushforwardCoherentEquivalence`: **Stacks 08AM**, that functor as an
  equivalence of categories, paired with the isomorphism identifying it with `i_*`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isClosedImmersion`: the direct image
  of a coherent module along a closed immersion into a locally Noetherian algebraic space is
  coherent.  This is what makes the target of the functor the *coherent* annihilated modules.
* `AlgebraicGeometry.Space.exists_isCoherent_modulePushforward_iso_of_annihilatedByKerIdeal`:
  a coherent `𝒪_X`-module annihilated by `ℐ` is the direct image of a coherent `𝒪_Z`-module.
* `AlgebraicGeometry.Space.fullyFaithfulPushforwardCoherent` and
  `AlgebraicGeometry.Space.essSurj_pushforwardCoherent`: the two halves of the equivalence.

## The proof

**Direct image preserves coherence.**  A closed immersion is finite (Stacks 081Y), hence
representable, so Stacks 060Z
(`AlgebraicGeometry.Space.isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite`)
applies to the quasi-coherent module `𝒢`: it is of finite type exactly when its base-change
direct image is, and that functor is `AlgebraicGeometry.Space.modulePushforward` by
`AlgebraicGeometry.Space.modulePushforwardChartIso`.  So `i_*𝒢` is of finite type; it is
quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion`, the
closed-immersion case of Stacks 03M9; and on a locally Noetherian algebraic space quasi-coherent
plus finite type is coherent, which is Stacks 07UB, conditions (1) and (2).

This route does **not** pass through an étale scheme chart, so it owes no chart case of
Stacks 03DW — the input that
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite_of_chartCase` carries as a
hypothesis for a general finite morphism.  Stacks 060Z replaces it: there the chart comparison is
performed on the *sections* over affine charts, where quasi-coherence supplies the base change
property of Descent, Proposition 03DX (2) directly.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` record the chart
case as the obstruction to the coherent target; it is not one.

**Essential surjectivity.**  Let `ℱ` be a coherent `𝒪_X`-module annihilated by `ℐ`.  The
essential-image clause of Stacks 08KS for algebraic spaces,
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`, puts `ℱ` in the
essential image of `i_*` on *all* modules, and in the unit form
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit`
that says the unit `ℱ ⟶ i_*i^*ℱ` of the adjunction of Stacks 03LU is an isomorphism.  So the
module on `Z` may be taken to be `i^*ℱ` itself, and `i^*ℱ` is coherent because `Z` is locally
Noetherian, by `AlgebraicGeometry.Space.isCoherent_modulePullback`.  Nothing further about the
inverse image is needed: the source instead writes `ℱ = i_*𝒢` for a quasi-coherent `𝒢` by
Stacks 04CJ and then checks coherence of `𝒢` étale-locally, which for this particular `𝒢` is
the coherence of a pullback.

## Implementation notes

The hypotheses `hX` and `hZ` are local Noetherianity of `X` and of `Z`, in the étale-local form
of Stacks 03E6.  Both are hypotheses of the source.  `hZ` is not derived from `hX`, although it
could be — a closed immersion is locally of finite type, so
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType`
would supply it — because the source states both and the derivation would add a dependency
without strengthening anything.

**Relation to the weaker statements already carried.**
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` carries
`@[stacks 08AM]` on two declarations whose target is the *larger* category of all `𝒪_X`-modules
annihilated by `ℐ`, with essential surjectivity not proved:
`AlgebraicGeometry.Space.coherentModulePushforward` and
`AlgebraicGeometry.Space.fullyFaithfulCoherentModulePushforward`.  Those statements are true and
are left as they stand; the full tag is stated here, by
`AlgebraicGeometry.Space.pushforwardCoherentEquivalence`, which is the only declaration in the
tree stating 08AM whole.

Full faithfulness is not reproved: the functor below composed with the inclusion of the full
subcategory is `AlgebraicGeometry.Space.modulePushforward` on the nose, which is fully faithful
by `AlgebraicGeometry.Space.fullyFaithfulModulePushforward` — Stacks 04CJ, part (2), the
`67.14.1` of the source's proof — and a full subcategory inclusion is fully faithful.

The scheme-level analogue, Stacks 087T, is formalized as
`Stacks.ClosedImmersion.pushforwardCohEquivalence`, and the assembly of the equivalence here
follows it.  It is *not* transported along the étale charts: coherence is not known to transfer
across `AlgebraicGeometry.Space.representedAssociatedModule`, so the case of schemes is not used
at all.

## References

* [Stacks Project, Lemma 69.12.8 (Tag 08AM)](https://stacks.math.columbia.edu/tag/08AM)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### Direct image preserves coherence -/

/-- **The direct image of a coherent module along a closed immersion is coherent.**  Let
`i : Z ⟶ X` be a closed immersion of algebraic spaces over `S` with `X` locally Noetherian and
let `𝒢` be a coherent `𝒪_Z`-module.  Then `i_*𝒢` is a coherent `𝒪_X`-module.

A closed immersion is finite by Stacks 081Y, so Stacks 060Z makes `i_*𝒢` of finite type — the
base-change direct image of that tag being `AlgebraicGeometry.Space.modulePushforward` by
`AlgebraicGeometry.Space.modulePushforwardChartIso` — and it is quasi-coherent by the
closed-immersion case of Stacks 03M9.  Quasi-coherent plus finite type is coherent on a locally
Noetherian algebraic space, by Stacks 07UB, conditions (1) and (2).

This is the case of a closed immersion of the coherence assertion of Stacks 07UH, which is
stated there for an arbitrary finite morphism and carries a chart case as a hypothesis; no
`@[stacks 07UH]` attribute is claimed. -/
theorem isCoherent_modulePushforward_of_isClosedImmersion
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : IsCoherent B S hS Z.1 Z.2 G) :
    IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj G) := by
  have hfin : IsFinite B S hS i.hom := isFinite_of_isClosedImmersion B S hS i.hom hi
  have hrep := relativelyRepresentable_hom_of_isFinite B S hS i hfin
  have _ : SheafOfModules.IsCoherentOnSite G := hG.toIsCoherentOnSite
  have hbc : ((smallBaseChangeModulePushforward.{u, u} B S hS i hrep).obj G).IsFiniteType :=
    (isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite B S hS i hfin G
      hG.toIsQuasicoherentOnSite).1 inferInstance
  have hft : ((modulePushforward B S hS i).obj G).IsFiniteType :=
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
      ((modulePushforwardChartIso B S hS i hrep).app G).symm hbc
  have _ : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2
    ((modulePushforward B S hS i).obj G)).2 ⟨?_, ?_⟩
  · exact isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi G
      hG.toIsQuasicoherentOnSite
  · exact Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType _ hft

/-! ### Essential surjectivity -/

/-- **A coherent `𝒪_X`-module annihilated by the ideal cutting out `Z` is the direct image of a
coherent `𝒪_Z`-module.**

The module on `Z` is `i^*ℱ`.  That `i_*i^*ℱ ≅ ℱ` is the essential-image clause of Stacks 08KS
for algebraic spaces read through the unit of the adjunction of Stacks 03LU, and `i^*ℱ` is
coherent because `Z` is locally Noetherian. -/
theorem exists_isCoherent_modulePushforward_iso_of_annihilatedByKerIdeal
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hann : AnnihilatedByKerIdeal B S hS i F) :
    ∃ G : Modules.{u, u} B S hS Z.1 Z.2, IsCoherent B S hS Z.1 Z.2 G ∧
      Nonempty ((modulePushforward B S hS i).obj G ≅ F) := by
  have _ : Fact (HasEtaleLocalProperty B S hS Z.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hZ⟩
  have _ : IsIso ((modulePullbackAdjunction B S hS i).unit.app F) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi F).1
      (essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi F hann)
  exact ⟨(modulePullback B S hS i).obj F, isCoherent_modulePullback B S hS i F hF,
    ⟨(asIso ((modulePullbackAdjunction B S hS i).unit.app F)).symm⟩⟩

/-! ### Stacks 08AM -/

/-- Coherent `𝒪_X`-modules annihilated by the ideal `ℐ = ker(i♯)` cutting out the closed
subspace, as a property of objects of the category of `𝒪_X`-modules.  Annihilation is
`AlgebraicGeometry.Space.AnnihilatedByKerIdeal`, which tests the sections of `ℐ` against the
module section by section. -/
abbrev coherentAnnihilatedByKerIdeal (i : Z ⟶ X) :
    ObjectProperty (Modules.{u, u} B S hS X.1 X.2) :=
  fun M => IsCoherent B S hS X.1 X.2 M ∧ AnnihilatedByKerIdeal B S hS i M

/-- **Stacks 08AM, the induced functor.**  Direct image along a closed immersion
`i : Z ⟶ X` of locally Noetherian algebraic spaces carries a coherent `𝒪_Z`-module to a coherent
`𝒪_X`-module annihilated by the ideal `ℐ` cutting out `Z`, hence induces a functor
`Coh(𝒪_Z) ⥤ {ℱ ∈ Coh(𝒪_X) | ℐℱ = 0}`.

Coherence of the direct image is
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isClosedImmersion` and annihilation is
part (3) of Stacks 04CJ,
`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`.  The tag is carried by the
equivalence below, which is the assertion of the source. -/
def pushforwardCoherent
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    CoherentModules.{u, u} B S hS Z.1 Z.2 ⥤
      (coherentAnnihilatedByKerIdeal B S hS i).FullSubcategory :=
  (coherentAnnihilatedByKerIdeal B S hS i).lift
    (ObjectProperty.ι _ ⋙ modulePushforward B S hS i)
    fun M ↦ ⟨isCoherent_modulePushforward_of_isClosedImmersion B S hS hX i hi M.obj M.property,
      annihilatedByKerIdeal_modulePushforward B S hS i M.obj⟩

/-- Forgetting coherence and annihilation identifies
`AlgebraicGeometry.Space.pushforwardCoherent` with direct image of modules.  This holds by
definition: the functor *is* that lift. -/
def pushforwardCoherentCompIso
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    pushforwardCoherent B S hS hX i hi ⋙
        ObjectProperty.ι (coherentAnnihilatedByKerIdeal B S hS i) ≅
      ObjectProperty.ι _ ⋙ modulePushforward B S hS i :=
  Iso.refl _

/-- **Full faithfulness of Stacks 08AM.**  Direct image along a closed immersion of algebraic
spaces is fully faithful from the coherent `𝒪_Z`-modules to the coherent `𝒪_X`-modules
annihilated by `ℐ`.

It is fully faithful on *all* modules by
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`, which is part (2) of Stacks 04CJ — the
lemma the source's proof cites for this half — and a full subcategory inclusion is fully
faithful. -/
def fullyFaithfulPushforwardCoherent
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (pushforwardCoherent B S hS hX i hi).FullyFaithful :=
  have := (fullyFaithfulModulePushforward B S hS i hi).full
  have := (fullyFaithfulModulePushforward B S hS i hi).faithful
  have : (pushforwardCoherent B S hS hX i hi).Faithful :=
    Functor.Faithful.of_comp_iso (pushforwardCoherentCompIso B S hS hX i hi)
  have : (pushforwardCoherent B S hS hX i hi).Full :=
    Functor.Full.of_comp_faithful_iso (pushforwardCoherentCompIso B S hS hX i hi)
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Essential surjectivity of Stacks 08AM.**  Every coherent `𝒪_X`-module annihilated by the
ideal `ℐ` cutting out `Z` is the direct image of a coherent `𝒪_Z`-module, by
`AlgebraicGeometry.Space.exists_isCoherent_modulePushforward_iso_of_annihilatedByKerIdeal`. -/
def essSurj_pushforwardCoherent
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (pushforwardCoherent B S hS hX i hi).EssSurj where
  mem_essImage N := by
    obtain ⟨G, hG, ⟨e⟩⟩ :=
      exists_isCoherent_modulePushforward_iso_of_annihilatedByKerIdeal B S hS hZ i hi
        N.obj N.property.1 N.property.2
    exact ⟨⟨G, hG⟩, ⟨(coherentAnnihilatedByKerIdeal B S hS i).isoMk e⟩⟩

/-- `AlgebraicGeometry.Space.pushforwardCoherent` is an equivalence: it is fully faithful and
essentially surjective. -/
def isEquivalence_pushforwardCoherent
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (pushforwardCoherent B S hS hX i hi).IsEquivalence :=
  Functor.IsEquivalence.mk
    (faithful := (fullyFaithfulPushforwardCoherent B S hS hX i hi).faithful)
    (full := (fullyFaithfulPushforwardCoherent B S hS hX i hi).full)
    (essSurj := essSurj_pushforwardCoherent B S hS hX hZ i hi)

/-- **Stacks 08AM.**  Let `S` be a scheme, let `i : Z ⟶ X` be a closed immersion of locally
Noetherian algebraic spaces over `S` and let `ℐ ⊆ 𝒪_X` be the quasi-coherent sheaf of ideals
cutting out `Z`.  The functor `i_*` induces an equivalence between the category of coherent
`𝒪_Z`-modules and the category of coherent `𝒪_X`-modules annihilated by `ℐ`.

The equivalence comes paired with the natural isomorphism identifying its functor, composed with
the inclusion of the full subcategory, with `AlgebraicGeometry.Space.modulePushforward` — so what
is asserted is that **`i_*` itself** is an equivalence onto the coherent annihilated modules, and
not merely that the two categories are equivalent.  The pairing is the shape in which the
scheme-level Stacks 087T is stated at
`Stacks.AlgebraicGeometry.Tag087TCoherentImage.coherentPushforwardEquivalence`.

The functor is `AlgebraicGeometry.Space.pushforwardCoherent`, its full faithfulness is
`AlgebraicGeometry.Space.fullyFaithfulPushforwardCoherent` — part (2) of Stacks 04CJ, the
`67.14.1` of the source's proof — and its essential surjectivity is
`AlgebraicGeometry.Space.essSurj_pushforwardCoherent`, which rests on coherence of the inverse
image together with the essential-image clause of Stacks 08KS for algebraic spaces.  That the
functor lands in the *coherent* annihilated modules is
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isClosedImmersion`. -/
@[stacks 08AM]
def pushforwardCoherentEquivalence
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    Σ e : CoherentModules.{u, u} B S hS Z.1 Z.2 ≌
        (coherentAnnihilatedByKerIdeal B S hS i).FullSubcategory,
      e.functor ⋙ ObjectProperty.ι (coherentAnnihilatedByKerIdeal B S hS i) ≅
        ObjectProperty.ι _ ⋙ modulePushforward B S hS i :=
  have := isEquivalence_pushforwardCoherent B S hS hX hZ i hi
  ⟨(pushforwardCoherent B S hS hX i hi).asEquivalence,
    pushforwardCoherentCompIso B S hS hX i hi⟩

end AlgebraicGeometry.Space

end
