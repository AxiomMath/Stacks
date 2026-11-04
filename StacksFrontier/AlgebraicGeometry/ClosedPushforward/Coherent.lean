module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.Topology.Sheaves.Modules.Coherent

/-!
# Direct image along a closed immersion, on coherent modules

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes and let `ℐ = ker(i^♯) ⊆ 𝒪_X`
be the quasi-coherent sheaf of ideals cutting out `Z`. Direct image carries coherent
`𝒪_Z`-modules to coherent `𝒪_X`-modules annihilated by `ℐ`, and the resulting functor

  `i_* : Coh(𝒪_Z) ⟶ {ℱ ∈ Coh(𝒪_X) | ℐℱ = 0}`

is an equivalence of categories.

## Main definitions

* `Stacks.ClosedImmersion.AnnihilatedByKer`: the kernel of the comorphism of `i` annihilates a
  module section by section, that is, `ℐℱ = 0`.
* `Stacks.ClosedImmersion.coherentAnnihilatedByKer`: coherence together with annihilation by
  `ℐ`, as a property of objects of the category of `𝒪_X`-modules.
* `Stacks.ClosedImmersion.pushforwardCoh`: direct image as a functor from coherent
  `𝒪_Z`-modules to the full subcategory it cuts out.

## Main results

* `Stacks.ClosedImmersion.pushforwardCohEquivalence`: that functor is an equivalence, which is
  [Stacks, Tag 087T].
* `Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`: annihilation by `ℐ` over every open
  is annihilation over the affine opens by Mathlib's quasi-coherent ideal sheaf
  `AlgebraicGeometry.Scheme.Hom.ker`, the ideal sheaf cutting out `Z`.
* `Stacks.ClosedImmersion.annihilatedByKer_of_forall_exists_affineOpen`: the same test run on a
  cofinal family of affine opens rather than on all of them, for consumers whose local data is
  available only around every point.
* `AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`: the source of a closed immersion
  into a locally Noetherian scheme is locally Noetherian, so the hypothesis
  `IsLocallyNoetherian Z` above is not an extra assumption.
* `AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`,
  `AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero` and
  `AlgebraicGeometry.exists_isCoherent_pushforward_iso_iff_smul_eq_zero`: the clauses of
  [Stacks, Tag 087T] in objectwise form, for consumers that want a module and an isomorphism
  rather than the functor.

## Implementation notes

The ideal sheaf cutting out `Z` is the kernel of `i^♯ : 𝒪_X ⟶ i_*𝒪_Z`, and a kernel of sheaves
is computed section by section, so `ℐ(U) = ker(Γ(X, U) ⟶ Γ(Z, i⁻¹U))` for *every* open `U`.
`AnnihilatedByKer` is therefore spelled with `i.app U`, which is the spelling the essential-image
statements of [Stacks, Tag 08KS] and [Stacks, Tag 01QY] already use in this directory. Mathlib's
`AlgebraicGeometry.Scheme.Hom.ker` packages the same ideal sheaf as a
`AlgebraicGeometry.Scheme.IdealSheafData`, which records ideals on the affine opens only;
`annihilatedByKer_iff_ker_ideal` identifies the two formulations, the substantial direction
being that annihilation of a section is a local condition and the affine opens form a basis.

The functor is obtained by lifting `AlgebraicGeometry.Scheme.Modules.pushforward i` — the direct
image of *all* modules — along the two assertions that make the lift possible: `i_*` of a
coherent module is coherent, which is
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff`, and it is
annihilated by `ℐ`, which is one direction of
`Stacks.ClosedImmersion.pushforward_essImage_iff`. Because the functor *is* that lift,
`pushforwardCoh_comp_ι` holds by definition: the equivalence below is the one induced by direct
image, and not an unrelated equivalence between the two categories.

Full faithfulness comes from the statement for all modules
(`Stacks.ClosedImmersion.fullyFaithfulPushforward`, [Stacks, Tag 08KS]) together with
faithfulness of the inclusion of a full subcategory. Essential surjectivity is where the
quasi-coherent statement is needed: a coherent `𝒪_X`-module killed by `ℐ` is quasi-coherent, so
[Stacks, Tag 01QY] produces a *quasi-coherent* `𝒪_Z`-module `𝒢` with `i_*𝒢 ≅ ℱ`, and then
`isCoherent_pushforward_iff` upgrades `𝒢` to a coherent module. Taking a preimage in all modules
instead would produce a module not known to be quasi-coherent, which is what [Stacks, Tag 01C4]
repairs in the source's proof.

`Coh(𝒪_Z)` is `AlgebraicGeometry.SheafOfModules.CoherentModules`, the full subcategory cut out
by the coherence predicate that the scheme-level coherence API of this library — in particular
[Stacks, Tag 01XZ] and `isCoherent_pushforward_iff` — is stated with. The library carries a
second, field-identical coherence predicate and a second category `Coh`; the two are identified
by `Stacks.SheafOfModules.isCoherent_iff_sheafOfModules_isCoherent` and
`Stacks.SheafOfModules.coherentModulesEquiv`, along which this equivalence transports.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.ClosedImmersionCoherence

universe u

namespace Stacks.ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The ideal sheaf `ℐ = ker(i^♯)` cutting out the closed subscheme annihilates the
`𝒪_X`-module `M`: over every open `U`, every function on `U` that dies under `i^♯` kills every
section of `M` over `U`.

A kernel of sheaves is computed section by section, so this is `ℐM = 0` for the quasi-coherent
sheaf of ideals `ℐ` cutting out `Z`; see `annihilatedByKer_iff_ker_ideal` for the identification
with Mathlib's `AlgebraicGeometry.Scheme.Hom.ker`. -/
def AnnihilatedByKer (M : X.Modules) : Prop :=
  ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0

/-- **Annihilation by the ideal sheaf cutting out `Z` may be tested on a cofinal family of affine
opens.** It is enough that every point of every open `U` have an affine open neighbourhood inside
`U` over which the ideal of `AlgebraicGeometry.Scheme.Hom.ker` annihilates the sections: a family
of affine opens that is cofinal in this sense is a basis of the topology, and annihilation of a
section is a local condition.

This is what a consumer whose local data is available only *around every point* needs, the ideal
of an effective Cartier divisor being principal on a neighbourhood of a point rather than on a
given affine open. The version for every affine open is
`Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`. -/
theorem annihilatedByKer_of_forall_exists_affineOpen [QuasiCompact i] (M : X.Modules)
    (h : ∀ (U : X.Opens) (x : X), x ∈ U → ∃ V : X.affineOpens, (V : X.Opens) ≤ U ∧
      x ∈ (V : X.Opens) ∧ ∀ a : Γ(X, (V : X.Opens)), a ∈ i.ker.ideal V →
        ∀ m : Γ(M, (V : X.Opens)), a • m = 0) :
    AnnihilatedByKer i M := by
  intro U a ha m
  refine M.isSheaf.section_ext (U := op U) (s := a • m) (t := 0) fun x hx => ?_
  obtain ⟨V, hVU, hxV, hV⟩ := h U x hx
  let g : op U ⟶ op (V : X.Opens) := (homOfLE hVU).op
  have ha' : (i.app (V : X.Opens)).hom ((X.presheaf.map g).hom a) = 0 := by
    simp only [NatTrans.naturality_apply, TopCat.Presheaf.pushforward_obj_obj,
      TopCat.Presheaf.pushforward_obj_map, ha, map_zero]
  have hz := hV ((X.presheaf.map g).hom a)
    (by rwa [i.ker_apply, RingHom.mem_ker]) ((M.val.map g).hom m)
  refine ⟨(V : X.Opens), hVU, hxV, ?_⟩
  show (M.val.map g).hom (a • m) = (M.val.map g).hom 0
  rw [map_zero]
  exact (M.val.map_smul g a m).trans hz

/-- **Annihilation by the ideal sheaf cutting out `Z` is tested on affine opens.** The ideal
sheaf `AlgebraicGeometry.Scheme.Hom.ker` records its ideals on the affine opens of `X` only, and
over an affine open it is the kernel of the comorphism; since annihilation of a section is a
local condition and the affine opens form a basis, the two conditions agree. -/
theorem annihilatedByKer_iff_ker_ideal [QuasiCompact i] (M : X.Modules) :
    AnnihilatedByKer i M ↔ ∀ (U : X.affineOpens) (a : Γ(X, (U : X.Opens))),
      a ∈ i.ker.ideal U → ∀ m : Γ(M, (U : X.Opens)), a • m = 0 := by
  refine ⟨fun h U a ha => h (U : X.Opens) a (RingHom.mem_ker.mp (i.ideal_ker_le U ha)),
    fun h => annihilatedByKer_of_forall_exists_affineOpen i M fun U x hx => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨⟨V, hV⟩, hVU, hxV, h ⟨V, hV⟩⟩

/-- Coherent `𝒪_X`-modules annihilated by the ideal sheaf cutting out `Z`, as a property of
objects of the category of `𝒪_X`-modules. -/
abbrev coherentAnnihilatedByKer : ObjectProperty X.Modules :=
  fun M => M.IsCoherent ∧ AnnihilatedByKer i M

variable [AlgebraicGeometry.IsClosedImmersion i]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- **[Stacks, Tag 087T], the induced functor.** Direct image along a closed immersion of
locally Noetherian schemes carries a coherent `𝒪_Z`-module to a coherent `𝒪_X`-module
annihilated by the ideal sheaf cutting out `Z`, hence induces a functor
`Coh(𝒪_Z) ⥤ {ℱ ∈ Coh(𝒪_X) | ℐℱ = 0}`. -/
@[stacks 087T "the induced functor"]
def pushforwardCoh :
    _root_.AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf ⥤
      (coherentAnnihilatedByKer i).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward i)
    fun M => by
      have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
      exact ⟨(isCoherent_pushforward_iff i M.obj).mpr M.property,
        (pushforward_essImage_iff i _).mp ((Scheme.Modules.pushforward i).obj_mem_essImage M.obj)⟩

/-- Forgetting coherence and annihilation identifies `Stacks.ClosedImmersion.pushforwardCoh`
with direct image of modules. -/
lemma pushforwardCoh_comp_ι :
    pushforwardCoh i ⋙ (coherentAnnihilatedByKer i).ι =
      ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward i := rfl

/-- Direct image along a closed immersion is fully faithful on coherent modules: it is fully
faithful on all modules by [Stacks, Tag 08KS], and the inclusion of a full subcategory is
faithful. -/
def fullyFaithfulPushforwardCoh : (pushforwardCoh i).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (coherentAnnihilatedByKer i).ι)
    (show (pushforwardCoh i ⋙ (coherentAnnihilatedByKer i).ι).FullyFaithful from
      (ObjectProperty.fullyFaithfulι _).comp (fullyFaithfulPushforward i))

/-- Direct image along a closed immersion is full on coherent modules. -/
instance pushforwardCoh_full : (pushforwardCoh i).Full :=
  (fullyFaithfulPushforwardCoh i).full

/-- Direct image along a closed immersion is faithful on coherent modules. -/
instance pushforwardCoh_faithful : (pushforwardCoh i).Faithful :=
  (fullyFaithfulPushforwardCoh i).faithful

/-- Direct image along a closed immersion is essentially surjective onto the coherent modules
annihilated by the ideal sheaf cutting out `Z`. Such a module is quasi-coherent, so
[Stacks, Tag 01QY] writes it as the direct image of a quasi-coherent `𝒪_Z`-module `𝒢`, and
coherence of `i_*𝒢` forces `𝒢` to be coherent. -/
instance pushforwardCoh_essSurj : (pushforwardCoh i).EssSurj where
  mem_essImage N := by
    have hNc : N.obj.IsCoherent := N.property.1
    have hNq : N.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent N.obj
    obtain ⟨G, ⟨e⟩⟩ := (pushforwardQcoh_essImage_iff i N.obj hNq).mpr N.property.2
    have : G.obj.IsQuasicoherent := G.property
    have e' : (Scheme.Modules.pushforward i).obj G.obj ≅ N.obj :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapIso e
    exact ⟨⟨G.obj, (isCoherent_pushforward_iff i G.obj).mp (isCoherent_of_iso e')⟩,
      ⟨(coherentAnnihilatedByKer i).isoMk e'⟩⟩

/-- Direct image along a closed immersion is an equivalence from coherent `𝒪_Z`-modules onto the
coherent `𝒪_X`-modules annihilated by the ideal sheaf cutting out `Z`. -/
instance pushforwardCoh_isEquivalence : (pushforwardCoh i).IsEquivalence where

/-- **[Stacks, Tag 087T].** Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes
and let `ℐ ⊆ 𝒪_X` be the quasi-coherent sheaf of ideals cutting out `Z`. Direct image along `i`
is an equivalence from the category of coherent `𝒪_Z`-modules to the category of coherent
`𝒪_X`-modules annihilated by `ℐ`.

The functor of this equivalence is `Stacks.ClosedImmersion.pushforwardCoh`, which composed with
the inclusion of the full subcategory *is* `AlgebraicGeometry.Scheme.Modules.pushforward i`, by
`pushforwardCoh_comp_ι`. -/
@[stacks 087T "the equivalence"]
def pushforwardCohEquivalence :
    _root_.AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf ≌
      (coherentAnnihilatedByKer i).FullSubcategory :=
  (pushforwardCoh i).asEquivalence

end Stacks.ClosedImmersion

/-! ### The clauses of Tag 087T in existential form

The equivalence above assumes local Noetherianity of `Z`; it is in fact implied by that of `X`,
which is `isLocallyNoetherian_of_isClosedImmersion` below. The remaining statements are the
objectwise form of the equivalence, for consumers that want a coherent module on `Z` and an
isomorphism rather than a functor. -/

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The source of a closed immersion into a locally Noetherian scheme is locally Noetherian.

The preimages of the affine opens of `X` cover `Z` and are affine, a closed immersion being an
affine morphism, and `Γ(Z, i⁻¹ U)` is a quotient of the Noetherian ring `Γ(X, U)` because
`i.app U` is surjective on an affine open. -/
theorem isLocallyNoetherian_of_isClosedImmersion
    [IsClosedImmersion i] [IsLocallyNoetherian X] : IsLocallyNoetherian Z := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun U : X.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩)
    (i.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)) fun U => ?_
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_surjective Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1)
    (i.app U.1).hom (i.app_surjective U.1 U.2)

/-- **[Stacks, Tag 087T], coherence of the direct image.** The direct image of a coherent
module along a closed immersion into a locally Noetherian scheme is coherent.

Local Noetherianity of the source is not assumed: it follows from that of the target by
`isLocallyNoetherian_of_isClosedImmersion`. -/
@[stacks 087T "coherence of the direct image"]
theorem isCoherent_pushforward_of_isClosedImmersion
    [IsClosedImmersion i] [IsLocallyNoetherian X] (G : Z.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pushforward i).obj G).IsCoherent :=
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  (isCoherent_pushforward_iff i G).mpr inferInstance

/-- **[Stacks, Tag 087T], essential surjectivity.** A coherent module on `X` annihilated,
section by section, by the kernel of the comorphism of a closed immersion `i : Z ⟶ X` is the
direct image along `i` of a coherent module on `Z`.

The module on `Z` is `i^* M`: it is coherent because `Z` is locally Noetherian and the pullback
of a coherent module is coherent, and the unit `M ⟶ i_* i^* M` is an isomorphism by
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`. -/
@[stacks 087T "essential surjectivity onto coherent modules"]
theorem exists_isCoherent_pushforward_iso_of_smul_eq_zero
    [IsClosedImmersion i] [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent]
    (h : ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0) :
    ∃ G : Z.Modules, G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward i).obj G ≅ M) := by
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i M h
  exact ⟨(Scheme.Modules.pullback i).obj M, isCoherent_pullback i M,
    ⟨(asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)).symm⟩⟩

/-- **[Stacks, Tag 087T], the essential image on coherent modules.** A coherent module on `X`
is the direct image of a coherent module on `Z` exactly when the kernel of the comorphism of
the closed immersion annihilates it section by section.

This is the characterisation of the essential image of `i_*` restricted to coherent modules:
the forward implication is the general essential-image criterion
`Stacks.ClosedImmersion.pushforward_essImage_iff`, which needs no coherence at all, and the
reverse one is `exists_isCoherent_pushforward_iso_of_smul_eq_zero`. -/
@[stacks 087T "the essential image on coherent modules"]
theorem exists_isCoherent_pushforward_iso_iff_smul_eq_zero
    [IsClosedImmersion i] [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] :
    (∃ G : Z.Modules, G.IsCoherent ∧
        Nonempty ((Scheme.Modules.pushforward i).obj G ≅ M)) ↔
      ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0 :=
  ⟨fun ⟨G, _, e⟩ => (Stacks.ClosedImmersion.pushforward_essImage_iff i M).1 ⟨G, e⟩,
    exists_isCoherent_pushforward_iso_of_smul_eq_zero i M⟩

end AlgebraicGeometry

end
