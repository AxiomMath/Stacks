module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ConstantOverAffineBase
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom

/-!
# An invertible module on projective space trivial on a fibre is trivial near that fibre

Let `A` be a Noetherian ring, `π : X ⟶ Spec A` proper and flat (for instance `X = ℙᵐ_A`), and
`ℒ` an invertible `𝒪_X`-module. Let `p` be a prime of `A` such that the pullback of `ℒ` to the
fibre `X_p` is trivial, and such that `X_p` has no higher cohomology of `𝒪` and only constant
global functions (for `X_p = ℙᵐ_{κ(p)}` these are the cohomology of projective space, Stacks
01XT). Then `ℒ` has a generating section over `π⁻¹(D(g))` for some `g ∉ p`.

This is the local content of the step of the proof of Stacks 0FH9 which the source attributes to
the projective space bundle formula: an invertible module on a projective space bundle which is
trivial on a fibre is trivial on a neighbourhood of that fibre.

## The argument

By cohomology and base change at a point with no higher fibre cohomology
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_cohomologyBaseChange`) the
pullback of sections `Γ(X, ℒ) ⟶ Γ(X_p, ℒ|_{X_p})` is a base change along `A ⟶ κ(p)`. The target
is `Γ(X_p, 𝒪) ≠ 0`, so some global section `s` of `ℒ` has nonzero restriction to the fibre. A
nonzero global section of the trivial module on a scheme whose global functions form a field
generates it, so `s` vanishes nowhere on `X_p`, hence (Stacks 0H78) nowhere along `π⁻¹(p)`. The
locus where `s` vanishes is closed, its image under the proper `π` is closed and misses `p`, so a
basic open `D(g) ∋ p` misses it, and `s` generates `ℒ` over `π⁻¹(D(g))` (Stacks 01CY).

## Main results

* `Stacks.ProjectiveBundle.subsingleton_rightDerived_unit_projectiveSpaceOver`: `ℙᵐ` over an
  affine base has no higher cohomology of `𝒪`.
* `Stacks.ProjectiveBundle.mem_nonvanishingLocus_of_iso_unit`: a nonzero global section of a
  trivial module vanishes nowhere, when the global functions form a field.
* `Stacks.ProjectiveBundle.exists_pullbackGlobalSections_ne_zero`: some global section of `ℒ`
  has nonzero restriction to the fibre.
* `Stacks.ProjectiveBundle.exists_generatorSections_preimage_basicOpen`: **the theorem.**

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.ProjectiveBundle

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit)

/-- **The structure sheaf of `ℙᵐ` over an affine base has no higher cohomology**, read off from
Serre's computation of the cohomology of the twists (Stacks 01XT) at the zeroth twist. -/
theorem subsingleton_rightDerived_unit_projectiveSpaceOver (m : ℕ) (W : Scheme.{u}) [IsAffine W]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (((moduleGlobalSections (projectiveSpaceOver m W)).rightDerived q).obj
      (SheafOfModules.unit (projectiveSpaceOver m W).ringCatSheaf)) := by
  have hz := Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology (↥(Γ(W, ⊤))) m 0 q
    (by omega)
  have hs : Subsingleton ((ModuleCat.restrictScalars
      ((projectiveSpaceOver m W ↘ W).appTop).hom).obj
        (((moduleGlobalSections (projectiveSpaceOver m W)).rightDerived q).obj
          (twistOver m W 0))) :=
    ModuleCat.subsingleton_of_isZero (hz.of_iso
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistCohomologyIsoRestrictScalars
        m W 0 q).symm)
  have hs' : Subsingleton (((moduleGlobalSections (projectiveSpaceOver m W)).rightDerived q).obj
      (twistOver m W 0)) := hs
  exact ModuleCat.subsingleton_of_isZero ((ModuleCat.isZero_of_subsingleton _).of_iso
    (((moduleGlobalSections (projectiveSpaceOver m W)).rightDerived q).mapIso
      (twistZeroIsoUnit m W)).symm)

/-- A base change of a module onto a nontrivial module is not the zero map.

The algebra and module structures are implicit rather than instance arguments, so that the
lemma applies to an `IsBaseChange` hypothesis stated with locally chosen structures. -/
theorem exists_apply_ne_zero_of_isBaseChange {R S M N : Type*} {_ : CommSemiring R}
    {_ : CommSemiring S} {_ : Algebra R S} {_ : AddCommMonoid M} {_ : Module R M}
    {_ : AddCommMonoid N} {_ : Module R N} {_ : Module S N} {_ : IsScalarTower R S N}
    {f : M →ₗ[R] N} (h : IsBaseChange S f) [Nontrivial N] :
    ∃ m, f m ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  refine hn (h.inductionOn (motive := fun n => n = 0) n (fun m => hc m) (fun s n hn => ?_)
    (fun n₁ n₂ h₁ h₂ => ?_))
  · rw [hn, smul_zero]
  · rw [h₁, h₂, add_zero]

/-- **A nonzero global section of a trivial module vanishes nowhere**, on a scheme whose global
functions form a field: it corresponds to a nonzero, hence invertible, global function. -/
theorem mem_nonvanishingLocus_of_iso_unit {Y : Scheme.{u}} (M : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (hfield : IsField Γ(Y, ⊤)) (t : Γ(M, ⊤))
    (ht : t ≠ 0) (y : Y) : y ∈ Stacks.Ample.nonvanishingLocus M t := by
  have hcomp' : ∀ z, e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) z) = z := fun z =>
    congrArg (fun φ => (φ.val.app (op ⊤)).hom z) e.hom_inv_id
  set c : Γ(Y, ⊤) := e.hom.val.app (op ⊤) t with hc_def
  have hc0 : c ≠ 0 := fun h => ht (by rw [← hcomp' t, ← hc_def, h]; exact map_zero _)
  have hcu : IsUnit c := by
    obtain ⟨d, hd⟩ := hfield.mul_inv_cancel hc0
    exact ⟨⟨c, d, hd, by rw [mul_comm]; exact hd⟩, rfl⟩
  let gO : GeneratorSections Y.toRingedSpace (SheafOfModules.unit Y.ringCatSheaf) ⊤ :=
    ⟨c, fun V h => by
      show Function.Bijective (fun r : Γ(Y, V) => r * Y.presheaf.map (homOfLE h).op c)
      exact IsUnit.isUnit_iff_mulRight_bijective.mp
        (hcu.map (Y.presheaf.map (homOfLE h).op).hom)⟩
  let gM : GeneratorSections Y.toRingedSpace M ⊤ :=
    generatorMapIso (X := Y.toRingedSpace) e.symm ⊤ gO
  have hgM : gM.val = t := hcomp' t
  have : ∀ w : Y.toRingedSpace.carrier, IsLocalRing
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace w) :=
    fun w => Y.isLocalRing w
  have : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property M :=
    isInvertible_of_isTrivial ⟨e⟩
  rw [← Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Y M t]
  have h := Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_generator M gM y
    (Opens.mem_top y)
  rw [hgM] at h
  show _ ∉ _
  rw [Stacks.NonvanishingSpelling.sectionsEquiv_symm_eval,
    show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  exact h

section NearFibre

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

/-- **Some global section has nonzero restriction to the fibre.** Under the hypotheses of
`exists_generatorSections_preimage_basicOpen`, the pullback of sections to the fibre is a base
change along `A ⟶ κ(p)` (cohomology and base change), and its target is nonzero. -/
theorem exists_pullbackGlobalSections_ne_zero [IsNoetherianRing A] [IsProper π] [Flat π]
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp π (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (e : (Scheme.Modules.pullback gp).obj L ≅ SheafOfModules.unit Xp.ringCatSheaf)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj (SheafOfModules.unit Xp.ringCatSheaf)))
    (hfield : IsField Γ(Xp, ⊤)) :
    ∃ s : Γ(L, ⊤), AlgebraicGeometry.pullbackGlobalSections gp L s ≠ 0 := by
  have hLag : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf _ L).mp hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have hflat : IsFlatOver π.toLRSHom.toShHom L := by
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree π L
  have hvan' : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj L)) :=
    fun i hi => ModuleCat.subsingleton_of_isZero
      ((@ModuleCat.isZero_of_subsingleton _ _ _ (hvan i hi)).of_iso
        (((moduleGlobalSections Xp).rightDerived i).mapIso e))
  obtain ⟨g, hg, n, H⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_cohomologyBaseChange π L hflat
      p hsq hvan'
  have hgu : IsUnit (algebraMap A p.ResidueField g) :=
    isUnit_iff_ne_zero.mpr fun h => hg (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hψ : (IsLocalization.Away.lift g hgu).comp (algebraMap A (Localization.Away g)) =
      algebraMap A p.ResidueField :=
    IsLocalization.Away.lift_comp g hgu
  obtain ⟨-, hBC, -⟩ := H (IsLocalization.Away.lift g hgu) (by rw [hψ]; exact hsq)
  have : Nontrivial Γ(Xp, ⊤) := ⟨hfield.exists_pair_ne⟩
  have : Nontrivial ((SheafOfModules.unit Xp.ringCatSheaf).val.obj (op ⊤)) :=
    inferInstanceAs (Nontrivial Γ(Xp, ⊤))
  have hinvinj : Function.Injective (e.inv.val.app (op ⊤)) := by
    intro a b hab
    have h := congrArg (e.hom.val.app (op ⊤)) hab
    have hc : ∀ z, e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) z) = z := fun z =>
      congrArg (fun φ => (φ.val.app (op ⊤)).hom z) e.inv_hom_id
    rwa [hc, hc] at h
  have : Nontrivial Γ((Scheme.Modules.pullback gp).obj L, gp ⁻¹ᵁ ⊤) := hinvinj.nontrivial
  obtain ⟨s, hs⟩ := exists_apply_ne_zero_of_isBaseChange hBC
  rw [Stacks.AlgebraicGeometry.ProperFlatGlobalSections.pullbackSectionsBaseₗ_top_apply] at hs
  exact ⟨s, hs⟩

/-- **A global section vanishing nowhere along a fibre generates near that fibre.** If the
pullback of a global section `s` of an invertible `ℒ` to the fibre `X_p` of the proper `π`
vanishes nowhere, then `s` generates `ℒ` over `π⁻¹(D(g))` for some `g ∉ p`: the image of the
vanishing locus of `s` is closed and misses `p`. -/
theorem exists_generatorSections_of_forall_mem_nonvanishingLocus [IsProper π] (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp π (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (s : Γ(L, ⊤)) (hall : ∀ y : Xp, gp y ∈ Stacks.Ample.nonvanishingLocus L s) :
    ∃ g : A, g ∉ p ∧
      Nonempty (GeneratorSections X.toRingedSpace L (π ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  have : Stacks.Ample.IsInvertibleModule X L := hL
  set Z : Set X := (Stacks.Ample.nonvanishingLocus L s)ᶜ with hZ_def
  have hZ : IsClosed Z := (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X L s).isClosed_compl
  have hpt : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ π '' Z := by
    rintro ⟨x, hxZ, hx⟩
    have hq : π x = Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
        (IsLocalRing.closedPoint p.ResidueField) := by
      rw [hx]
      refine PrimeSpectrum.ext ?_
      show p = Ideal.comap (algebraMap A p.ResidueField) (IsLocalRing.maximalIdeal _)
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
        Ideal.ker_algebraMap_residueField]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ hq
    refine hxZ ?_
    have h := hall (hsq.isoPullback.inv z)
    rwa [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst, hz] at h
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpt
      (π.isClosedMap Z hZ).isOpen_compl
  refine ⟨g, hpg, ⟨⟨L.presheaf.map
    (homOfLE (le_top : π ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ ⊤)).op s, fun V hV => ?_⟩⟩⟩
  have hVnv : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s := by
    intro x hx
    by_contra hxZ
    exact hsub (hV hx) ⟨x, hxZ, rfl⟩
  show Function.Bijective (fun r : Γ(X, V) => r • L.presheaf.map (homOfLE hV).op
    (L.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ ⊤)).op s))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact Stacks.NonvanishingSpelling.bijective_smul X L s hVnv

/-- **An invertible module trivial on a fibre is trivial near that fibre.** Let `A` be Noetherian,
`π : X ⟶ Spec A` proper and flat, `ℒ` invertible on `X` and `p` a prime of `A` such that the
pullback of `ℒ` to the fibre `X_p` is trivial, `X_p` has no higher cohomology of `𝒪` and the
global functions on `X_p` form a field. Then `ℒ` has a generating section over `π⁻¹(D(g))` for
some `g ∉ p`. -/
theorem exists_generatorSections_preimage_basicOpen [IsNoetherianRing A] [IsProper π] [Flat π]
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp π (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (htriv : Nonempty ((Scheme.Modules.pullback gp).obj L ≅ SheafOfModules.unit Xp.ringCatSheaf))
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj (SheafOfModules.unit Xp.ringCatSheaf)))
    (hfield : IsField Γ(Xp, ⊤)) :
    ∃ g : A, g ∉ p ∧
      Nonempty (GeneratorSections X.toRingedSpace L (π ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  obtain ⟨e⟩ := htriv
  obtain ⟨s, hs⟩ := exists_pullbackGlobalSections_ne_zero π L hL p hsq e hvan hfield
  refine exists_generatorSections_of_forall_mem_nonvanishingLocus π L hL p hsq s fun y => ?_
  refine (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff gp L s y).mp ?_
  rw [← Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection]
  exact mem_nonvanishingLocus_of_iso_unit _ e hfield _ hs y

end NearFibre

end Stacks.ProjectiveBundle

end
