module

public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.FibreLift
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# An invertible module trivial on a fibre is trivial near it

Let `f : X ⟶ Y` be a proper morphism onto a locally Noetherian scheme and let `y` be a closed
point of `Y` whose fibre `X_y` has dimension at most one and satisfies `H¹(X_y, 𝒪_{X_y}) = 0`.
This file proves that an invertible `𝒪_X`-module `ℒ` with `ℒ|_{X_y} ≅ 𝒪_{X_y}` is trivial on
`f⁻¹(V)` for some open neighbourhood `V` of `y`. This is the heart of [Stacks, Tag 0E24].

Over an affine open `U = Spec R` around `y`, the point `y` is a maximal ideal `𝔪` and the fibre
`X_y` is the closed subscheme of `f⁻¹(U)` cut out by `𝔪 𝒪`
(`Stacks.PicardFibreTrivial.exists_isIso_comp_fromSpec`, from the fibre square). The generator
of `ℒ|_{X_y}` lifts to a section `s` of `ℒ` over `f⁻¹(U)`
(`Stacks.PicardFibreTrivial.surjective_unit_app_top_of_isProper`, the theorem on formal
functions). By [Stacks, Tag 0H78] `s` vanishes at no point of `X_y`, so its nonvanishing locus is
an open neighbourhood of the fibre on which `ℒ` is trivial ([Stacks, Tag 01CY]), and since `f` is
closed that neighbourhood contains `f⁻¹(V)` for a neighbourhood `V` of `y`.

## Main results

* `Stacks.PicardFibreTrivial.exists_isIso_comp_fromSpec`: the residue field at a closed point of
  an affine open `Spec R` is `R/𝔪`, compatibly with the maps to the scheme.
* `Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber`: the triviality near the fibre.

## References

* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

universe u

namespace Stacks.PicardFibreTrivial

/-- **The residue field at a closed point of an affine open is the quotient by the maximal
ideal**, compatibly with the two maps to the scheme: for `x` a maximal ideal of `R = Γ(Y, U)`,
`Spec (R/𝔪_x) ⟶ Spec R ⟶ Y` is `Spec κ(y) ⟶ Y` precomposed with an isomorphism, where `y` is
the image of `x`. -/
theorem exists_isIso_comp_fromSpec {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (x : Spec Γ(Y, U)) [x.asIdeal.IsMaximal] :
    ∃ ψ : Spec (.of (Γ(Y, U) ⧸ x.asIdeal)) ⟶ Spec (Y.residueField (hU.fromSpec x)), IsIso ψ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal)) ≫ hU.fromSpec =
        ψ ≫ Y.fromSpecResidueField (hU.fromSpec x) := by
  let β : Spec (.of x.asIdeal.ResidueField) ⟶ Spec (.of (Γ(Y, U) ⧸ x.asIdeal)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Γ(Y, U) ⧸ x.asIdeal) x.asIdeal.ResidueField))
  have : IsIso β := by
    let e : CommRingCat.of (Γ(Y, U) ⧸ x.asIdeal) ≅ CommRingCat.of x.asIdeal.ResidueField :=
      (RingEquiv.ofBijective _
        x.asIdeal.bijective_algebraMap_quotient_residueField).toCommRingCatIso
    exact inferInstanceAs (IsIso (Spec.map e.hom))
  let α := Spec.map (Scheme.Spec.residueFieldIso Γ(Y, U) x).inv
  have hαβ : α ≫ β ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal)) =
      (Spec Γ(Y, U)).fromSpecResidueField x := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  refine ⟨inv (α ≫ β) ≫ Spec.map (hU.fromSpec.residueFieldMap x), inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, IsIso.eq_inv_comp,
    ← hαβ]
  simp only [Category.assoc]

/-- A point of an affine open whose image is a closed point is a maximal ideal. -/
theorem isMaximal_of_isClosed_fromSpec {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (x : Spec Γ(Y, U)) (hy : IsClosed ({hU.fromSpec x} : Set Y)) : x.asIdeal.IsMaximal := by
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  have h := hy.preimage hU.fromSpec.continuous
  rw [show hU.fromSpec.base ⁻¹' {hU.fromSpec x} = {x} from
    Set.ext fun z => ⟨fun hz => hinj hz, fun hz => hz ▸ rfl⟩] at h
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 h

/-- The fibre of `f` over a closed point `x` of an affine open `U = Spec R` is a closed
subscheme of `f⁻¹(U)` cut out by `𝔪_x 𝒪`. -/
theorem exists_isClosedImmersion_fiber_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (x : Spec Γ(Y, U)) [x.asIdeal.IsMaximal] :
    ∃ i : f.fiber (hU.fromSpec x) ⟶ (f ⁻¹ᵁ U).toScheme, IsClosedImmersion i ∧
      i ≫ (f ⁻¹ᵁ U).ι = f.fiberι (hU.fromSpec x) ∧
      i.ker = baseIdealSheaf Γ(Y, U) x.asIdeal
        (f ∣_ U ≫ hU.isoSpec.hom : (f ⁻¹ᵁ U).toScheme ⟶ Spec (.of Γ(Y, U))) ∧
      ∀ a ∈ x.asIdeal, i.appTop (baseRingHom Γ(Y, U)
        (f ∣_ U ≫ hU.isoSpec.hom : (f ⁻¹ᵁ U).toScheme ⟶ Spec (.of Γ(Y, U))) a) = 0 := by
  let ιU := (f ⁻¹ᵁ U).ι
  let g : (f ⁻¹ᵁ U).toScheme ⟶ Spec (.of Γ(Y, U)) := f ∣_ U ≫ hU.isoSpec.hom
  let q₁ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))
  have : IsClosedImmersion q₁ := IsClosedImmersion.spec_of_quotient_mk (R := Γ(Y, U)) x.asIdeal
  obtain ⟨ψ, hψ, hψeq⟩ := exists_isIso_comp_fromSpec hU x
  have hright : IsPullback ιU g f hU.fromSpec :=
    (isPullback_morphismRestrict f U).flip.of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec
      (Iso.refl _) (by simp [ιU]) (by simp [g]) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, ← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc])
  have hbig : IsPullback (pullback.fst g q₁ ≫ ιU) (pullback.snd g q₁ ≫ ψ) f
      (Y.fromSpecResidueField (hU.fromSpec x)) := by
    have h1 := (IsPullback.of_hasPullback g q₁).paste_horiz hright
    rw [hψeq] at h1
    exact h1.of_iso (Iso.refl _) (Iso.refl _) (asIso ψ) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  let φ := hbig.isoPullback
  let i : f.fiber (hU.fromSpec x) ⟶ (f ⁻¹ᵁ U).toScheme := φ.inv ≫ pullback.fst g q₁
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (φ.inv ≫ pullback.fst g q₁))
  refine ⟨i, inferInstance, hbig.isoPullback_inv_fst, ?_, fun a ha => ?_⟩
  · change (φ.inv ≫ pullback.fst g q₁).ker = _
    rw [Scheme.Hom.ker_comp_of_isIso,
      ← Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst]
  · refine appTop_baseRingHom_eq_zero Γ(Y, U) g x.asIdeal i (φ.inv ≫ pullback.snd g q₁) ?_ ha
    change (φ.inv ≫ pullback.fst g q₁) ≫ g = _
    rw [Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm

/-- Let `g : Z ⟶ Spec R` be proper with `R` Noetherian and `i : Z₀ ⟶ Z` a closed immersion with
ideal sheaf `𝔪 𝒪_Z`, where `dim Z₀ ≤ 1` and `H¹(Z₀, 𝒪_{Z₀}) = 0`; an invertible `𝒪_Z`-module
trivial on `Z₀` is trivial on an open neighbourhood of `Z₀`. -/
theorem exists_restrict_iso_unit_of_isClosedImmersion (R : Type u) [CommRing R]
    [IsNoetherianRing R] {Z Z₀ : Scheme.{u}} (g : Z ⟶ Spec (.of R)) [IsProper g] (m : Ideal R)
    (F : Z.Modules)
    [Stacks.SheafOfModules.IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property F]
    (i : Z₀ ⟶ Z) [IsClosedImmersion i] (hi : i.ker = baseIdealSheaf R m g)
    (hi0 : ∀ a ∈ m, i.appTop (baseRingHom R g a) = 0) (hdim : topologicalKrullDim Z₀ ≤ 1)
    (hH1 : IsZero ((coh Z₀ 1).obj (SheafOfModules.unit Z₀.ringCatSheaf)))
    (ε : (Scheme.Modules.pullback i).obj F ≅ SheafOfModules.unit Z₀.ringCatSheaf) :
    ∃ W : Z.Opens, (∀ z, i.base z ∈ W) ∧
      Nonempty (F.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have hFag : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      Z.ringCatSheaf.property F :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ ‹_›
  have hFag' : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj
      Z.ringCatSheaf.property F := hFag
  have : F.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible F
  have hF : Stacks.SheafOfModules.IsCoherent F :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ F)
  let one : Γ(SheafOfModules.unit Z₀.ringCatSheaf, ⊤) := (1 : Γ(Z₀, ⊤))
  obtain ⟨s, hs⟩ := surjective_unit_app_top_of_isProper R g m F hF i hi hi0 hdim
    (hH1.of_iso ((coh _ 1).mapIso ε)) (ε.inv.app ⊤ one)
  -- It vanishes at no point of the fibre, [Stacks, Tag 0H78].
  have hτ : Stacks.Ample.nonvanishingLocus _ (ε.inv.app ⊤ one) = Set.univ :=
    (Stacks.Ample.nonvanishingLocus_congr ε.symm _).trans
      (Stacks.Models.nonvanishingLocus_unit_one _)
  have h := (Stacks.Models.nonvanishingLocus_unit_app_top i F s).symm.trans
    ((congrArg (Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj F)) hs).trans hτ)
  -- So `ℒ` is trivial on the nonvanishing locus `W` of `s`, [Stacks, Tag 01CY].
  let s' := (Stacks.NonvanishingSpelling.sectionsEquiv _ F).symm s
  refine ⟨Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) F s', fun z => ?_,
    Stacks.SheafOfModules.nonempty_restrictIsoUnit_of_le_nonvanishingOpen _ F s' _ le_rfl⟩
  change i.base z ∈ Stacks.SheafOfModules.nonvanishingLocus _ s'
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
  exact (Set.ext_iff.mp h z).mpr trivial

/-- For `f` closed, an open set containing the fibre over `y` contains `f⁻¹(V)` for an open
neighbourhood `V` of `y`. -/
theorem exists_preimage_le_of_fiber_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedMap f.base) (W : X.Opens) (y : Y) (h : ∀ p, f.base p = y → p ∈ W) :
    ∃ V : Y.Opens, y ∈ V ∧ f ⁻¹ᵁ V ≤ W := by
  let T := f.base '' ((W : Set X)ᶜ)
  have hT : IsClosed T := hf _ W.isOpen.isClosed_compl
  have hyT : y ∉ T := fun ⟨p, hp, hpy⟩ => hp (h p hpy)
  exact ⟨⟨Tᶜ, hT.isOpen_compl⟩, hyT, fun p hp => by_contra fun hn => hp ⟨p, hn, rfl⟩⟩

/-- **An invertible module trivial on the fibre over a closed point is trivial near it.** Let
`f : X ⟶ Y` be proper with `Y` locally Noetherian and let `y` be a closed point of `Y` with
`dim X_y ≤ 1` and `H¹(X_y, 𝒪_{X_y}) = 0`. If `ℒ` is an invertible `𝒪_X`-module with
`ℒ|_{X_y} ≅ 𝒪_{X_y}`, then `ℒ` is trivial on `f⁻¹(V)` for some open neighbourhood `V` of `y`. -/
theorem exists_restrict_iso_unit_of_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdim : topologicalKrullDim (f.fiber y) ≤ 1)
    (hH1 : IsZero ((coh (f.fiber y) 1).obj (SheafOfModules.unit (f.fiber y).ringCatSheaf)))
    (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (e : (Scheme.Modules.pullback (f.fiberι y)).obj L ≅
      SheafOfModules.unit (f.fiber y).ringCatSheaf) :
    ∃ V : Y.Opens, y ∈ V ∧ Nonempty (L.restrict (f ⁻¹ᵁ V).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  classical
  -- An affine open `U = Spec R` around `y`, in which `y` is a maximal ideal `x`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  obtain ⟨x, rfl⟩ : ∃ x, hU.fromSpec x = y := ⟨_, hU.fromSpec_primeIdealOf ⟨y, hyU⟩⟩
  have := isMaximal_of_isClosed_fromSpec hU x hy
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let ιU := (f ⁻¹ᵁ U).ι
  let g : (f ⁻¹ᵁ U).toScheme ⟶ Spec (.of Γ(Y, U)) := f ∣_ U ≫ hU.isoSpec.hom
  have : IsProper (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsProper f› U
  have : IsProper g := inferInstance
  obtain ⟨i, _, hiι, hi, hi0⟩ := exists_isClosedImmersion_fiber_preimage f hU x
  let F := (Scheme.Modules.pullback ιU).obj L
  obtain ⟨W, hW, ⟨eW⟩⟩ := exists_restrict_iso_unit_of_isClosedImmersion Γ(Y, U) g x.asIdeal F i
    hi hi0 hdim hH1
    ((Scheme.Modules.pullbackComp i ιU).app L ≪≫ (Scheme.Modules.pullbackCongr hiι).app L ≪≫ e)
  let W' : X.Opens := ιU ''ᵁ W
  have eW' : L.restrict (Scheme.Opens.ι W') ≅
      SheafOfModules.unit (Scheme.Opens.toScheme W').ringCatSheaf :=
    Stacks.SheafOfModules.restrictIsoUnitOfIsoOver L (k₁ := Scheme.Opens.ι W ≫ ιU)
      (ιU.isoImage W) (ιU.isoImage_hom_ι W)
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι W ≫ ιU)).app L ≪≫
        ((Scheme.Modules.pullbackComp (Scheme.Opens.ι W) ιU).app L).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι W)).app F).symm ≪≫ eW)
  have hfibre : ∀ p : X, f.base p = hU.fromSpec x → p ∈ W' := by
    intro p hp
    obtain ⟨z, rfl⟩ : p ∈ Set.range (f.fiberι (hU.fromSpec x)).base := by
      rwa [Scheme.Hom.range_fiberι]
    refine ⟨i.base z, hW z, ?_⟩
    rw [← hiι]
    rfl
  obtain ⟨V, hyV, hle⟩ := exists_preimage_le_of_fiber_subset f f.isClosedMap W' _ hfibre
  exact ⟨V, hyV, ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L hle eW'⟩⟩

end Stacks.PicardFibreTrivial

end
