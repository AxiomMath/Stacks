module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticSupport
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer

/-!
# The scheme-theoretic support of a coherent module

The annihilator of a coherent module on a locally Noetherian scheme is an ideal sheaf, and the
closed subscheme it cuts out is the *scheme-theoretic support* of the module: the module is the
direct image of a coherent module there, and that module has full support.

## Main definitions

* `AlgebraicGeometry.annihilatorIdeal`: the ideal sheaf whose ideal on an affine open is the
  annihilator of the sections there.

## Main results

* `AlgebraicGeometry.ideal_annihilatorIdeal`: the ideal of `annihilatorIdeal` on an affine open
  really is the annihilator of the sections, with no saturation lost.
* `AlgebraicGeometry.exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal`: the module
  is the direct image of a coherent module on its scheme-theoretic support.
* `AlgebraicGeometry.supp_eq_support_annihilatorIdeal`: the support of the module is the support
  of its annihilator ideal sheaf, so the scheme-theoretic support carries the topological one.
* `AlgebraicGeometry.supp_eq_univ_of_pushforward_iso_annihilatorIdeal`: a module on the
  scheme-theoretic support whose direct image is the given module has full support.
* `AlgebraicGeometry.hasNoEmbeddedPoints_subscheme_annihilatorIdeal`: if the module has no
  embedded associated points, the scheme-theoretic support has no embedded points.

## Implementation notes

**The annihilator family is an ideal sheaf on the nose, not a saturation of one.** The
`map_ideal_basicOpen` field is `annihilator_map_basicOpen`: the sections of a quasi-coherent
module over a basic open are the localization of the sections over the affine open
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, the module half
of [Stacks, Tag 01P7]) and the annihilator of a finite module extends along a flat ring map to
the annihilator of the base change (`ann_extension_eq_ann_baseChange_module`, [Stacks, Tag
07T8]). Because the family verifies the field directly, `annihilatorIdeal` is built as the
structure rather than through `Scheme.IdealSheafData.ofIdeals`, and `ideal_annihilatorIdeal` —
that the ideal on an affine open *is* the annihilator, with nothing lost — holds by `rfl`. Every
affine-local computation below is therefore with the honest annihilator. Finiteness of the
sections, which Tag 07T8 needs, is `moduleFinite_sections`.

**Where the source's "coherent sheaf of ideals" clause went.**
[Stacks, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM) states the defining ideal as the
kernel of `𝒪_X ⟶ SheafHom(ℱ, ℱ)` and asserts that it is coherent. Neither the internal
endomorphism sheaf of a module nor the coherence of the annihilator subsheaf
([Stacks, Tag 0H2L](https://stacks.math.columbia.edu/tag/0H2L)) exists in the library, so that
clause is not stated here and carries no attribute. What *is* stated is the ideal sheaf with the
same affine ideals, which is what the downstream consumers of Tag 02OM use: the closed subscheme
and the descended module.

**The descent is Tag 087T, not a second construction.** Once
`annihilatorIdeal_smul_eq_zero` says that the kernel of the comorphism of
`(annihilatorIdeal ℱ).subschemeι` annihilates `ℱ`,
`AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero` supplies a *coherent*
module on the subscheme with the right direct image in one step. The source instead descends to
a quasi-coherent module of finite type and then upgrades; taking the coherent form off the shelf
removes the finite-type bookkeeping entirely.

**Clause (b) of the source is not here.** That the descended module inherits the absence of
embedded associated points needs the associated points of a direct image along an affine
morphism to be the image of the associated points
([Stacks, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)), which the library does not have.

## References

* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02M8](https://stacks.math.columbia.edu/tag/02M8)
* [Stacks Project, Tag 00L2](https://stacks.math.columbia.edu/tag/00L2)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- For a flat ring map that is a localization and a finite module, the extension of the
annihilator is the annihilator of the localized module.

This is `ann_extension_eq_ann_baseChange_module` (Tag 07T8) transported along the base-change
description of a localized module. -/
private theorem annihilator_map_of_isLocalizedModule (R A M N : Type*) [CommRing R]
    [CommRing A] {S : Submonoid R} [Algebra R A] [IsLocalization S A]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    {f : M →ₗ[R] N} [IsLocalizedModule S f] :
    Ideal.map (algebraMap R A) (Module.annihilator R M) = Module.annihilator A N := by
  have : Module.Flat R A := IsLocalization.flat A S
  rw [ann_extension_eq_ann_baseChange_module]
  exact (IsLocalizedModule.isBaseChange S A f).equiv.annihilator_eq

/-- The annihilators of the sections of a coherent module are compatible with restriction to a
basic open: this is the `map_ideal_basicOpen` field of an ideal sheaf for the annihilator
family. -/
theorem annihilator_map_basicOpen [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (U : X.affineOpens) (f : Γ(X, U.1)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (Module.annihilator Γ(X, U.1) Γ(F, U.1)) =
      Module.annihilator Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) := by
  have hle : X.basicOpen f ≤ U.1 := X.basicOpen_le f
  have _ : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections F U
  let _ := algebraOfLE X hle
  let _ := moduleOfLE F hle
  let _ := isScalarTowerOfLE F hle
  have _ : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have _ : F.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  have _ : IsLocalizedModule (Submonoid.powers f) (restrictₗ F hle) :=
    isLocalizedModule_restrictₗ F U.2 f rfl hle
  exact annihilator_map_of_isLocalizedModule (S := Submonoid.powers f)
    Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, U.1) Γ(F, X.basicOpen f)
    (f := restrictₗ F hle)

/-- **[Stacks, Tag 02OM] the ideal sheaf cutting out the scheme-theoretic support.** The
annihilators of the sections of a coherent module on a locally Noetherian scheme form an ideal
sheaf; the closed subscheme it cuts out is the scheme-theoretic support of the module. -/
@[stacks 02OM "the ideal sheaf cutting out the support",
  ega "IV 4.6.16",
  ega "IV 4.6.18",
  sga "4 XVII 6.3.4" "special case"]
noncomputable def annihilatorIdeal [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(F, U.1)
  map_ideal_basicOpen U f := annihilator_map_basicOpen F U f

/-- The ideal of `annihilatorIdeal F` on an affine open is the annihilator of the sections
there. -/
@[simp]
theorem ideal_annihilatorIdeal [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (U : X.affineOpens) :
    (annihilatorIdeal F).ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1) :=
  rfl

/-- The kernel of the comorphism of the scheme-theoretic support annihilates the module, section
by section.

This is the hypothesis of the coherent descent of [Stacks, Tag 087T]. Both the claim and the
annihilator are affine-local, so a section killed by the comorphism is killed on every affine
open of a basis, and sections of a sheaf that vanish locally vanish. -/
theorem annihilatorIdeal_smul_eq_zero [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens) (a : Γ(X, U)) (ha : ((annihilatorIdeal F).subschemeι.app U).hom a = 0)
    (m : Γ(F, U)) : a • m = 0 := by
  apply F.isSheaf.section_ext (U := op U)
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, hxV, ?_⟩
  set i := (annihilatorIdeal F).subschemeι
  have hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := fun z hz => hVU hz
  have hmap : i.appLE V (i ⁻¹ᵁ V) le_rfl (X.presheaf.map (homOfLE hVU).op a) = 0 := by
    have h₁ : i.appLE U (i ⁻¹ᵁ U) le_rfl a = 0 := by
      simpa [Scheme.Hom.appLE] using ha
    have hrestrict : i.appLE U (i ⁻¹ᵁ V) hpre a = 0 := by
      have hcomp := congrArg (fun f => f.hom a)
        (i.appLE_map (U := U) (V := i ⁻¹ᵁ U) le_rfl (homOfLE hpre).op)
      rw [CommRingCat.hom_comp, RingHom.comp_apply, h₁] at hcomp
      simpa [Scheme.Hom.appLE] using hcomp.symm
    have hlocal := congrArg (fun f => f.hom a)
      (i.map_appLE (U := V) (U' := U) (V := i ⁻¹ᵁ V) le_rfl (homOfLE hVU).op)
    simpa [Scheme.Hom.appLE] using hlocal.trans hrestrict
  have hmemAnn : X.presheaf.map (homOfLE hVU).op a ∈
      Module.annihilator Γ(X, V) Γ(F, V) := by
    rw [← ideal_annihilatorIdeal F ⟨V, hV⟩, ← (annihilatorIdeal F).ker_subschemeι_app ⟨V, hV⟩]
    simpa [Scheme.Hom.appLE] using hmap
  calc F.presheaf.map (homOfLE hVU).op (a • m)
      = X.presheaf.map (homOfLE hVU).op a • F.presheaf.map (homOfLE hVU).op m :=
        F.map_smul (homOfLE hVU) a m
    _ = 0 := Module.mem_annihilator.mp hmemAnn _
    _ = F.presheaf.map (homOfLE hVU).op 0 := by simp

/-- **[Stacks, Tag 02OM], the descended module.** A coherent module on a locally Noetherian
scheme is the direct image of a coherent module on its scheme-theoretic support.

This is [Stacks, Tag 087T]'s coherent descent applied to `annihilatorIdeal_smul_eq_zero`. -/
@[stacks 02OM "existence of the coherent module on the support"]
theorem exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ G : (annihilatorIdeal F).subscheme.Modules, G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward (annihilatorIdeal F).subschemeι).obj G ≅ F) :=
  exists_isCoherent_pushforward_iso_of_smul_eq_zero (annihilatorIdeal F).subschemeι F
    (annihilatorIdeal_smul_eq_zero F)

/-- On an affine open, the zero locus of the annihilator of the sections is the support of the
sections as a module.

This is Tag 00L2 (`Module.support_eq_zeroLocus`) transported from `PrimeSpectrum Γ(X, U)` to the
affine open along `IsAffineOpen.fromSpec`, which matches basic opens on the two sides. -/
@[sga "2 III 1.2" "special case"]
private theorem mem_zeroLocus_annihilator_iff [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (U : X.affineOpens) {x : X} (hxU : x ∈ U.1) :
    x ∈ X.zeroLocus (U := U.1) (Module.annihilator Γ(X, U.1) Γ(F, U.1)) ↔
      U.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U.1) Γ(F, U.1) := by
  have _ : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections F U
  set p := U.2.primeIdealOf ⟨x, hxU⟩
  have hpoint : U.2.fromSpec p = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hbasic (s : Γ(X, U.1)) : x ∈ X.basicOpen s ↔ p ∈ PrimeSpectrum.basicOpen s := by
    rw [← hpoint, ← U.2.fromSpec_preimage_basicOpen s]
    rfl
  rw [Scheme.mem_zeroLocus_iff, Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  simp only [SetLike.mem_coe, Set.subset_def]
  refine ⟨fun h s hs => ?_, fun h s hs hx => ?_⟩
  · by_contra hsp
    exact h s hs ((hbasic s).2 ((PrimeSpectrum.mem_basicOpen s p).2 hsp))
  · exact (PrimeSpectrum.mem_basicOpen s p).1 ((hbasic s).1 hx) (h s hs)

/-- **[Stacks, Tag 02OM], the support of the scheme-theoretic support.** The support of a
coherent module is the support of its annihilator ideal sheaf — so the closed subscheme cut out
by the annihilator has the support of the module as its underlying set.

No attribute: the source's clause (c) is about the support of the *descended* module, which is
`supp_eq_univ_of_pushforward_iso_annihilatorIdeal`; this is the ingredient, not the clause. -/
@[ega "III 4.1.10" "partial"]
theorem supp_eq_support_annihilatorIdeal [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    SheafOfModules.supp F = ((annihilatorIdeal F).support : Set X) := by
  have _ : F.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h₃ : x ∈ (annihilatorIdeal F).support ↔
      x ∈ X.zeroLocus (U := U) ((annihilatorIdeal F).ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hxU
  exact (Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ x hxU).symm.trans
    ((mem_zeroLocus_annihilator_iff F ⟨U, hU⟩ hxU).symm.trans h₃.symm)

/-- **[Stacks, Tag 02OM], full support on the scheme-theoretic support.** A module on the
scheme-theoretic support whose direct image is the given coherent module has support the whole
subscheme.

The subscheme's underlying set is the support of the module by
`supp_eq_support_annihilatorIdeal`, so every point of it lies in the support of `ℱ`; being in the
support is nontriviality of the stalk, and the stalk of `ℱ` at the image of `z` is the stalk of
`𝒢` at `z` because the comparison map of a pushforward along an inducing map is an
isomorphism.

No attribute: this is the source's clause (c), but conditional on being handed the direct-image
isomorphism, so it states no clause of the tag on its own. The unconditional form is
`exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints`. -/
theorem supp_eq_univ_of_pushforward_iso_annihilatorIdeal [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (G : (annihilatorIdeal F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (annihilatorIdeal F).subschemeι).obj G ≅ F) :
    SheafOfModules.supp G = Set.univ := by
  set i := (annihilatorIdeal F).subschemeι
  ext z
  simp only [Set.mem_univ, iff_true]
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk
    (X := TopCat.of (annihilatorIdeal F).subscheme)
    (R := (annihilatorIdeal F).subscheme.ringCatSheaf) (F := G)]
  have hx : i.base z ∈ SheafOfModules.supp F := by
    rw [supp_eq_support_annihilatorIdeal F, ← (annihilatorIdeal F).range_subschemeι]
    exact ⟨z, rfl⟩
  have hF : Nontrivial (((Scheme.Modules.toPresheaf X).obj F).stalk (i.base z)) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F (i.base z)).mp hx
  set T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (i.base z)
  have _ : Nontrivial (T.obj F) := hF
  set ψ := (T.mapIso e.symm).hom
  have _ : IsIso ψ := inferInstance
  have hpush :
      Nontrivial ((i.base _* (Scheme.Modules.toPresheaf _).obj G).stalk (i.base z)) := by
    show Nontrivial (T.obj ((Scheme.Modules.pushforward i).obj G))
    obtain ⟨a, b, hab⟩ := exists_pair_ne (T.obj F)
    exact ⟨ConcreteCategory.hom ψ a, ConcreteCategory.hom ψ b,
      fun heq => hab ((ConcreteCategory.bijective_of_isIso ψ).1 heq)⟩
  set P := (Scheme.Modules.toPresheaf (annihilatorIdeal F).subscheme).obj G
  set α := P.stalkPushforward Ab i.base z
  have _ : IsIso α := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    Ab i.isClosedEmbedding.isInducing P z
  obtain ⟨a, b, hab⟩ := hpush
  exact ⟨ConcreteCategory.hom α a, ConcreteCategory.hom α b,
    fun heq => hab ((ConcreteCategory.bijective_of_isIso α).1 heq)⟩

/-! ### Absence of embedded points on the scheme-theoretic support -/

/-- Over a Noetherian ring the two spellings of an associated prime agree. -/
private theorem associatedPrime_mem_iff_stacks {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] {p : Ideal R} :
    p ∈ associatedPrimes R M ↔ IsAssociatedPrimeStacks R M p := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  exact ⟨fun ⟨hp, m, hm⟩ => ⟨hp, m, by simpa only [Submodule.colon_span] using hm.symm⟩,
    fun ⟨hp, m, hm⟩ => ⟨hp, m, by simpa only [Submodule.colon_span] using hm.symm⟩⟩

/-- The sections of a coherent module over an affine open of a locally Noetherian scheme have no
embedded associated primes as soon as the module has no embedded associated points.

The points of the affine open corresponding to two nested associated primes are associated points
of the module, and the one belonging to the smaller prime specializes to the other, so they would
witness an embedded associated point. -/
private theorem sections_hasNoEmbeddedAssociatedPrimes [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (hF : HasNoEmbeddedAssociatedPoints F)
    (U : X.Opens) (hU : IsAffineOpen U) :
    HasNoEmbeddedAssociatedPrimes Γ(X, U) Γ(F, U) := by
  have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  intro p hp q hq hqp
  have hpStack : IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) p := associatedPrime_mem_iff_stacks.mp hp
  have hqStack : IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) q := associatedPrime_mem_iff_stacks.mp hq
  set xp : PrimeSpectrum Γ(X, U) := ⟨p, hpStack.1⟩
  set xq : PrimeSpectrum Γ(X, U) := ⟨q, hqStack.1⟩
  have hxU : hU.fromSpec xp ∈ U := hU.range_fromSpec.subset ⟨xp, rfl⟩
  have hyU : hU.fromSpec xq ∈ U := hU.range_fromSpec.subset ⟨xq, rfl⟩
  have hpx : hU.primeIdealOf ⟨hU.fromSpec xp, hxU⟩ = xp :=
    hU.fromSpec.isOpenEmbedding.injective (by rw [hU.fromSpec_primeIdealOf])
  have hqx : hU.primeIdealOf ⟨hU.fromSpec xq, hyU⟩ = xq :=
    hU.fromSpec.isOpenEmbedding.injective (by rw [hU.fromSpec_primeIdealOf])
  have hxAssoc : Stacks.Divisors.IsAssociatedPoint F (hU.fromSpec xp) :=
    (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU hxU).mp
      (by rw [hpx]; exact hpStack)
  have hyAssoc : Stacks.Divisors.IsAssociatedPoint F (hU.fromSpec xq) :=
    (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU hyU).mp
      (by rw [hqx]; exact hqStack)
  have hspec : hU.fromSpec xq ⤳ hU.fromSpec xp :=
    ((PrimeSpectrum.le_iff_specializes xq xp).mp hqp).map hU.fromSpec.continuous
  by_contra hne
  exact hF (hU.fromSpec xp) ⟨hxAssoc, hU.fromSpec xq, hyAssoc, hspec, fun hyx =>
    hne (congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective hyx))⟩

/-- **[Stacks, Tag 02OM], no embedded points on the support.** If a coherent module on a locally
Noetherian scheme has no embedded associated points, then the closed subscheme cut out by its
annihilator has no embedded points.

The subscheme's ring of functions over the preimage of an affine open `U` is
`Γ(X, U) ⧸ Ann Γ(F, U)`, which has no embedded primes by Tag 02M8 because `Γ(F, U)` has none by
`sections_hasNoEmbeddedAssociatedPrimes`; an embedded point of the subscheme would give two
nested associated primes there. -/
@[stacks 02OM "absence of embedded points on the support"]
theorem hasNoEmbeddedPoints_subscheme_annihilatorIdeal [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) :
    HasNoEmbeddedPoints (annihilatorIdeal F).subscheme := by
  set I := annihilatorIdeal F
  set Z := I.subscheme
  set ι := I.subschemeι
  have _ : F.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  have _ : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion ι
  intro z hz
  obtain ⟨hz, y, hy, hspec, hne⟩ := hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ι z)) isOpen_univ
  have hVaff : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
  have hzV : z ∈ ι ⁻¹ᵁ U := hxU
  have hyV : y ∈ ι ⁻¹ᵁ U := (hspec.map ι.continuous).mem_open U.2 hxU
  have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hNoQuot : HasNoEmbeddedAssociatedPrimes
      (Γ(X, U) ⧸ Module.annihilator Γ(X, U) Γ(F, U))
      (Γ(X, U) ⧸ Module.annihilator Γ(X, U) Γ(F, U)) :=
    have _ : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections F ⟨U, hU⟩
    hasNoEmbeddedAssociatedPrimes_quotient_annihilator Γ(X, U) Γ(F, U)
      (sections_hasNoEmbeddedAssociatedPrimes F hF U hU)
  have _ : IsNoetherianRing Γ(Z, ι ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨ι ⁻¹ᵁ U, hVaff⟩
  have hNoV : HasNoEmbeddedAssociatedPrimes Γ(Z, ι ⁻¹ᵁ U) Γ(Z, ι ⁻¹ᵁ U) :=
    AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_of_ringEquiv
      ((I.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv.trans
        (Ideal.quotientEquivAlgOfEq Γ(X, U) (ideal_annihilatorIdeal F ⟨U, hU⟩)))
      hNoQuot
  have _ : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isCoherent (SheafOfModules.unit Z.ringCatSheaf)).1
  have hp : (hVaff.primeIdealOf ⟨z, hzV⟩).asIdeal ∈
      associatedPrimes Γ(Z, ι ⁻¹ᵁ U) Γ(Z, ι ⁻¹ᵁ U) :=
    associatedPrime_mem_iff_stacks.mpr
      ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
        (SheafOfModules.unit Z.ringCatSheaf) (ι ⁻¹ᵁ U) hVaff hzV).mpr hz)
  have hq : (hVaff.primeIdealOf ⟨y, hyV⟩).asIdeal ∈
      associatedPrimes Γ(Z, ι ⁻¹ᵁ U) Γ(Z, ι ⁻¹ᵁ U) :=
    associatedPrime_mem_iff_stacks.mpr
      ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
        (SheafOfModules.unit Z.ringCatSheaf) (ι ⁻¹ᵁ U) hVaff hyV).mpr hy)
  have hqle : (hVaff.primeIdealOf ⟨y, hyV⟩).asIdeal ≤ (hVaff.primeIdealOf ⟨z, hzV⟩).asIdeal := by
    refine (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hVaff.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp ?_)
    simpa only [IsAffineOpen.fromSpec_primeIdealOf] using hspec
  have hpoint := congrArg hVaff.fromSpec (PrimeSpectrum.ext (hNoV hp hq hqle))
  exact hne (by simpa only [IsAffineOpen.fromSpec_primeIdealOf] using hpoint)

/-- **[Stacks, Tag 02OM].** A coherent module without embedded associated points on a locally
Noetherian scheme is the direct image of a coherent module on a closed subscheme without
embedded points, and that module has full support.

This is the source's statement with clause (b) — that the descended module itself has no embedded
associated points — omitted; see the module docstring. -/
@[stacks 02OM "the descended module on a support without embedded points"]
theorem exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) :
    HasNoEmbeddedPoints (annihilatorIdeal F).subscheme ∧
      ∃ G : (annihilatorIdeal F).subscheme.Modules, G.IsCoherent ∧
        SheafOfModules.supp G = Set.univ ∧
        Nonempty ((Scheme.Modules.pushforward (annihilatorIdeal F).subschemeι).obj G ≅ F) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal F
  exact ⟨hasNoEmbeddedPoints_subscheme_annihilatorIdeal F hF,
    G, hG, supp_eq_univ_of_pushforward_iso_annihilatorIdeal F G e, ⟨e⟩⟩

end AlgebraicGeometry

end
