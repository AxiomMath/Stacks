module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FibreSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyOpenSubfunctor

/-!
# Twisting a class with invertible direct image so that the direct image is trivial

Let `π : Y ⟶ T` be proper, flat and of finite presentation and `c` a Picard class of `Y` whose
representative `ℳ` has `Rπ_*ℳ` an invertible module `𝒩` placed in degree zero. For `n = -[𝒩]`
the representative `ℒ` of `c + π^*n` has `π_*ℒ ≅ 𝒪_T`, by the projection formula for an invertible
module ([Stacks, Tag 01E8]); and over every affine open of `T` on which `n` is trivial, `ℒ` has no
higher cohomology. Consequently the section `e(1)` of `ℒ` restricts to a generator of
`H⁰(Y_t, ℒ_t)`, which is one-dimensional, on every fibre, and `ℒ_t` has no higher cohomology.

This is the first step of the proof of the claim in [Stacks, Tag 0B9X], where the section is the
one corresponding to the adjunction map `π^*𝒩 ⟶ ℳ`.

## Main results

* `AlgebraicGeometry.exists_iso_unit_pushforward_picardRepresentative`: the twist.
* `AlgebraicGeometry.subsingleton_rightDerived_pullback_ι`: no higher cohomology over affine
  opens on which the twist is trivial.
* `AlgebraicGeometry.pullbackGlobalSections_fiberι_ne_zero_of_iso` and
  `AlgebraicGeometry.cohomologyOverField_fiber_of_iso`: the fibres.

No Stacks tag is attached.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable {Y T : Scheme.{u}} (π : Y ⟶ T)

/-- The direct image of a module whose derived direct image is a finite locally free module of
rank one in degree zero is invertible. -/
theorem exists_pushforward_iso_of_hasDerivedPushforwardRank {M : Y.Modules}
    (h : HasDerivedPushforwardRank π M 0 1) :
    ∃ (N : T.Modules) (_hN : Stacks.SheafOfModules.IsInvertible T.presheaf
      (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N),
      Nonempty ((Scheme.Modules.pushforward π).obj M ≅ N) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  exact ⟨N, Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one T.toRingedSpace N,
    ⟨pushforwardIsoOfIsoSingle e⟩⟩

open Stacks.Picard in
/-- **Twisting by a class from the base makes the direct image trivial.** If `Rπ_*ℳ` is an
invertible module `𝒩` placed in degree zero, then for `n = -[𝒩]` the direct image of the chosen
representative of `[ℳ] + π^*n` is isomorphic to `𝒪_T`. -/
theorem exists_iso_unit_pushforward_picardRepresentative (c : ofScheme Y)
    (hc : HasDerivedPushforwardRank π (Stacks.Picard.picardRepresentative _ c).obj 0 1) :
    ∃ n : ofScheme T, Nonempty ((SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅
      (Scheme.Modules.pushforward π).obj
        (Stacks.Picard.picardRepresentative _ (c + schemePullbackClass π n)).obj) := by
  obtain ⟨N, hN, ⟨eπ⟩⟩ := exists_pushforward_iso_of_hasDerivedPushforwardRank π hc
  set n : ofScheme T := -Stacks.SheafOfModules.picardClass T.presheaf
    (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N hN
  refine ⟨n, ?_⟩
  set M := (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj
  set N' := (Stacks.Picard.picardRepresentative T.toRingedSpace n).obj
  have hN' := (Stacks.Picard.picardRepresentative T.toRingedSpace n).property
  have hM := (Stacks.Picard.picardRepresentative Y.toRingedSpace c).property
  have : Stacks.SheafOfModules.IsInvertible T.presheaf
      (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N' := hN'
  have : Stacks.SheafOfModules.IsInvertible T.presheaf
      (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N := hN
  have : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M := hM
  -- `𝒩 ⊗ 𝒩' ≅ 𝒪_T`
  have hNN' := Stacks.SheafOfModules.tensorProduct_isInvertible T.presheaf
    (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N N'
  have hcl : Stacks.SheafOfModules.picardClass T.presheaf
      (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) _ hNN' = 0 := by
    refine (Stacks.SheafOfModules.picardClass_tensorSheaf T.presheaf
      (Stacks.RingedSpace.structureIsSheaf T.toRingedSpace) N N' hN hN' hNN').symm.trans ?_
    have := classOf_picardRepresentative T.toRingedSpace n
    change _ + Stacks.SheafOfModules.picardClass _ _ N' hN' = 0
    rw [this]
    exact add_neg_cancel _
  obtain ⟨i4⟩ := (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ hNN').1 hcl
  -- `ℒ ≅ ℳ ⊗ π^*𝒩'`
  set L := (Stacks.Picard.picardRepresentative Y.toRingedSpace (c + schemePullbackClass π n)).obj
  have hL :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace (c + schemePullbackClass π n)).property
  have hpN' := Stacks.RingedSpace.modulePullback_isInvertible_of π.toLRSHom.toShHom N' hN'
  have : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor π.toLRSHom.toShHom).obj N') := hpN'
  have hMN' := Stacks.SheafOfModules.tensorProduct_isInvertible Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M
    ((Stacks.RingedSpace.pullbackFunctor π.toLRSHom.toShHom).obj N')
  have hcl' : Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL =
      Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) _ hMN' := by
    refine (classOf_picardRepresentative Y.toRingedSpace _).trans ?_
    refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_tensorSheaf Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M _ hM hpN' hMN')
    rw [← pullbackClass_classOf π.toLRSHom.toShHom N' hN']
    change c + schemePullbackClass π n = _ + pullbackClass π.toLRSHom.toShHom
      (Stacks.SheafOfModules.picardClass _ _ _
        (Stacks.Picard.picardRepresentative T.toRingedSpace n).property)
    rw [classOf_picardRepresentative, classOf_picardRepresentative]
  obtain ⟨i1⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ hL hMN').1 hcl'
  have : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.sheaf.obj
      (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace).property N' := hN'
  have i2 := Stacks.ProjectionFormula.projectionFormulaIso π.toLRSHom.toShHom M N'
  have i3 := ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).mapIso eπ).app N'
  exact ⟨i4.symm ≪≫ i3.symm ≪≫ i2 ≪≫ (Scheme.Modules.pushforward π).mapIso i1.symm⟩

open Stacks.Picard in
/-- **An affine open on which a class of the base is trivial**, around any point. -/
theorem exists_isAffineOpen_schemePullbackClass_eq_zero (n : ofScheme T) (t : T) :
    ∃ V : T.Opens, IsAffineOpen V ∧ t ∈ V ∧ schemePullbackClass V.ι n = 0 := by
  obtain ⟨U, htU, hU⟩ := exists_mem_schemePullbackClass_eq_zero n t
  obtain ⟨V, hV, htV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens T) htU
  refine ⟨V, hV, htV, ?_⟩
  rw [← Scheme.homOfLE_ι T hVU, ← schemePullbackClass_comp, hU]
  exact map_zero (schemePullbackClassHom (T.homOfLE hVU))

open Stacks.Picard in
/-- **No higher cohomology over a trivializing affine open.** If `Rπ_*ℳ` is a module placed in
degree zero, `π` is proper and of finite presentation, `ℳ` is the representative of `c` and `V` is
an affine open of `T` on which `n` is trivial, then the representative of `c + π^*n` has no higher
cohomology on `π⁻¹(V)`. -/
theorem subsingleton_rightDerived_pullback_ι [Flat π] [IsProper π] (hfp : FinitePresentation π)
    (c : ofScheme Y)
    (hc : HasDerivedPushforwardRank π (Stacks.Picard.picardRepresentative _ c).obj 0 1)
    (n : ofScheme T) {V : T.Opens} (hV : IsAffineOpen V) (hn : schemePullbackClass V.ι n = 0)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
      ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj
        (Stacks.Picard.picardRepresentative _ (c + schemePullbackClass π n)).obj)) := by
  obtain ⟨N₀, -, ⟨eN⟩⟩ := hc
  set M : Y.Modules := (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj
  have hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace c).property
  obtain ⟨hMfp, hMflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible π M hM
  obtain ⟨e'⟩ := nonempty_iso_single_of_isOpenImmersion π V.ι (π ∣_ V) (π ⁻¹ᵁ V).ι
    (isPullback_morphismRestrict π V).flip hfp M hMfp hMflat eN
  have : IsAffine V.toScheme := hV
  have : SheafOfModules.IsQuasicoherent M := Stacks.Picard.isQuasicoherent_of_isInvertible M hM
  have : ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj M).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ M
  have hvanM := subsingleton_rightDerived_of_iso_single e' p hp
  -- the two pulled-back classes agree
  have hcl : schemePullbackClass (π ⁻¹ᵁ V).ι (c + schemePullbackClass π n) =
      schemePullbackClass (π ⁻¹ᵁ V).ι c := by
    rw [schemePullbackClass_add, schemePullbackClass_comp, ← morphismRestrict_ι,
      ← schemePullbackClass_comp, hn]
    exact add_eq_left.2 (map_zero (schemePullbackClassHom (π ∣_ V)))
  obtain ⟨e1⟩ := Stacks.RigidifiedPicard.nonempty_iso_pullback_picardRepresentative
    (π ⁻¹ᵁ V).ι (c + schemePullbackClass π n)
  obtain ⟨e2⟩ := Stacks.RigidifiedPicard.nonempty_iso_pullback_picardRepresentative
    (π ⁻¹ᵁ V).ι c
  rw [hcl] at e1
  exact ModuleCat.subsingleton_of_isZero ((@ModuleCat.isZero_of_subsingleton _ _ _ hvanM).of_iso
    (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).mapIso (e1 ≪≫ e2.symm)))

/-- The inverse of an isomorphism `𝒪_T ≅ π_*ℒ` sends the restriction to `V` of the image of `1`
to `1`. -/
private theorem unit_inv_app_pushforward_hom_app_one (L : Y.Modules)
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    (V : T.Opens) :
    Scheme.Modules.Hom.app e.inv V
      (((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))) = (1 : Γ(T, V)) := by
  have hnat := PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : V ≤ ⊤)).op
    (1 : Γ(T, ⊤))
  have h1 : ((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤))) =
      Scheme.Modules.Hom.app e.hom V (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op 1) :=
    hnat.symm
  rw [h1, map_one]
  exact congr(Scheme.Modules.Hom.app $(Iso.hom_inv_id e) V (1 : Γ(T, V)))

/-- **The section `e(1)` of a module with `𝒪_T ≅ π_*ℒ` is nonzero on every fibre**, as soon as
every point of `T` has an affine neighbourhood over which `ℒ` has no higher cohomology. -/
theorem pullbackGlobalSections_fiberι_ne_zero_of_iso [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    (hvan : ∀ t : T, ∃ V : T.Opens, IsAffineOpen V ∧ t ∈ V ∧ ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))
    (t : T) :
    pullbackGlobalSections (π.fiberι t) L
      (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤))) ≠ 0 := by
  obtain ⟨V, hV, htV, hv⟩ := hvan t
  refine pullbackGlobalSections_fiberι_ne_zero π hV L hL hv _
    (Scheme.Modules.Hom.app e.inv V).hom (fun a z => Scheme.Modules.Hom.app_smul e.inv a z) ?_ t htV
  exact unit_inv_app_pushforward_hom_app_one π L e V

/-- **The cohomology of the fibres of a module with `𝒪_T ≅ π_*ℒ`**, under the hypotheses of
`pullbackGlobalSections_fiberι_ne_zero_of_iso`: no higher cohomology, and one-dimensional global
sections. -/
theorem cohomologyOverField_fiber_of_iso [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    (hvan : ∀ t : T, ∃ V : T.Opens, IsAffineOpen V ∧ t ∈ V ∧ ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))
    (t : T) :
    (∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) p)) ∧
    Module.finrank (T.residueField t) (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) 0) = 1 := by
  obtain ⟨V, hV, htV, hv⟩ := hvan t
  refine cohomologyOverField_fiber_of_bijective π hV L hL hv
    (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))
    (Scheme.Modules.Hom.app e.inv V).hom (fun a z => Scheme.Modules.Hom.app_smul e.inv a z) ?_
    (Function.bijective_iff_has_inverse.2 ⟨Scheme.Modules.Hom.app e.hom V,
      fun y => congr(Scheme.Modules.Hom.app $(Iso.inv_hom_id e) V y),
      fun x => congr(Scheme.Modules.Hom.app $(Iso.hom_inv_id e) V x)⟩) t htV
  exact unit_inv_app_pushforward_hom_app_one π L e V

end AlgebraicGeometry

end
