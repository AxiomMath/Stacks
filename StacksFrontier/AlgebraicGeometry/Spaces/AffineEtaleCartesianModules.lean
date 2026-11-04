module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Quasi-coherent modules on the affine étale site are cartesian

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. A sheaf of
modules on the affine étale site of `F` over its structure sheaf is *cartesian* when each of its
restriction maps exhibits its target as a base change of its source. A quasi-coherent sheaf of
modules on the affine étale site is cartesian.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleRingSheaf` is the sheaf of rings underlying the affine
  étale structure sheaf.

## Main results

* `AlgebraicGeometry.Space.affineEtaleStructurePresheaf_eq`: the affine étale structure presheaf
  is the presheaf of global regular functions on the underlying affine schemes, with sections
  raised to the universe of the site.
* `AlgebraicGeometry.Space.flat_affineEtaleStructurePresheaf_map` and
  `AlgebraicGeometry.Space.isPushout_affineEtaleStructurePresheaf`: the structure presheaf is
  flat along every morphism of the site and turns fibre products into pushouts of rings.
* `AlgebraicGeometry.Space.affineEtale_covering_finite_flat`: the covering families of the affine
  étale site are finite and flat on the underlying schemes.
* `AlgebraicGeometry.Space.isSheaf_of_cartesian_affineEtale` and
  `AlgebraicGeometry.Space.isSheaf_of_cartesian_affineEtale_over`: a cartesian presheaf of
  modules on the affine étale site, or on a slice of it, is a sheaf.
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_affineEtale_of_cover`: being cartesian is
  local on a covering of the affine étale site.
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_over_of_hasGlobalPresentation`: a global
  presentation on a slice makes the module cartesian there.
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`: a
  quasi-coherent sheaf of modules on the affine étale site of an algebraic space is cartesian.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 0H03](https://stacks.math.columbia.edu/tag/0H03)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

/-- Raising the universe of the source and target of a flat ring homomorphism keeps it flat. -/
private theorem RingHom.Flat.ulift {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {g : R₀ →+* S₀} (hg : g.Flat) : (g.ulift.{m, m}).Flat := by
  have h : g.ulift.{m, m} =
      (ULift.ringEquiv : ULift.{m} S₀ ≃+* S₀).symm.toRingHom.comp
        (g.comp (ULift.ringEquiv : ULift.{m} R₀ ≃+* R₀).toRingHom) := rfl
  rw [h]
  exact RingHom.Flat.comp
    (RingHom.Flat.comp (RingHom.Flat.of_bijective ULift.ringEquiv.bijective) hg)
    (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sheaf of rings underlying the structure sheaf of the affine étale site of `F`. -/
noncomputable abbrev affineEtaleRingSheaf :
    Sheaf (AffineEtale.topology B S hS F) RingCat.{u + 1} :=
  (sheafCompose (AffineEtale.topology B S hS F)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (affineEtaleStructureSheaf B S hS F hF)

/-- The structure presheaf of the affine étale site of `F` is the presheaf of global regular
functions on the underlying affine schemes, with its sections raised to the universe of the
étale charts. -/
theorem affineEtaleStructurePresheaf_eq :
    (affineEtaleStructureSheaf B S hS F hF).obj =
      Stacks.Sites.liftedSchemeRings.{u, u + 1, u + 1, u} (AffineEtale.toScheme B S hS F) := by
  show (AffineEtale.inclusion B S hS F).op ⋙
      (liftedStructureSheaf B S hS F).val.obj = _
  rw [(liftedStructureSheaf B S hS F).property]
  rfl

/-- The structure presheaf of the affine étale site is flat along every morphism of the site. -/
theorem flat_affineEtaleStructurePresheaf_map {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    (((affineEtaleStructureSheaf B S hS F hF).obj.map f.op)).hom.Flat := by
  rw [affineEtaleStructurePresheaf_eq B S hS F hF]
  have := AffineEtale.flat_toScheme_map B S hS F f
  exact RingHom.Flat.ulift
    (Scheme.Hom.flat_appTop ((AffineEtale.toScheme B S hS F).map f))

/-- A fibre product square of affine étale charts gives a pushout square of the structure
rings. -/
theorem isPushout_affineEtaleStructurePresheaf
    {X Y Z P : AffineEtale B S hS F}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout ((affineEtaleStructureSheaf B S hS F hF).obj.map a.op)
      ((affineEtaleStructureSheaf B S hS F hF).obj.map b.op)
      ((affineEtaleStructureSheaf B S hS F hF).obj.map fst.op)
      ((affineEtaleStructureSheaf B S hS F hF).obj.map snd.op) := by
  rw [affineEtaleStructurePresheaf_eq B S hS F hF]
  exact CommRingCat.isPushout_ulift (isPushout_appTop_of_isPullback
    (Functor.map_isPullback (AffineEtale.toScheme B S hS F) h))

/-- The image on underlying schemes of a covering family of affine étale charts is a flat
covering. -/
private theorem presieve₀_map_toScheme_mem_flat {U : AffineEtale B S hS F}
    {E : PreZeroHypercover.{u + 1} U} (hE : AffineEtale.IsCovering B S hS F ⟨U, E⟩) :
    (E.map (AffineEtale.toScheme B S hS F)).presieve₀ ∈
      Scheme.precoverage @Flat ((AffineEtale.toScheme B S hS F).obj U) := by
  obtain ⟨hs, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (AffineEtale.toScheme B S hS F))).mp hE.1.2
  exact (Scheme.presieve₀_mem_precoverage_iff _).mpr
    ⟨hs, fun i => by have := het i; infer_instance⟩

/-- The covering families of the affine étale site of `F` are finite, and on the underlying
schemes they are flat coverings of affine schemes. -/
theorem affineEtale_covering_finite_flat {U : AffineEtale B S hS F} (P : Presieve U)
    (hP : P ∈ AffineEtale.precoverage B S hS F U) :
    P.uncurry.Finite ∧ P.map (AffineEtale.toScheme B S hS F) ∈
      Scheme.precoverage @Flat ((AffineEtale.toScheme B S hS F).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  have := hE.2
  refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
  rw [← PreZeroHypercover.presieve₀_map]
  exact presieve₀_map_toScheme_mem_flat B S hS F hE

/-- A cartesian presheaf of modules on the affine étale site of `F` is a sheaf. -/
theorem isSheaf_of_cartesian_affineEtale
    (M : PresheafOfModules.{max m (u + 1)}
      ((affineEtaleStructureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (AffineEtale B S hS F)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m} M f)) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf := by
  refine Stacks.PresheafOfModules.isSheaf_of_affine_flat_covers.{u, u + 1, m, u + 1, u}
    (AffineEtale.toScheme B S hS F) (affineEtaleStructureSheaf B S hS F hF).obj
    (affineEtaleStructurePresheaf_eq B S hS F hF) M hM
    (AffineEtale.precoverage B S hS F) ?_
  intro U P hP
  obtain ⟨E, rfl, hE⟩ := hP
  refine ⟨E, rfl, hE.2, ?_⟩
  exact presieve₀_map_toScheme_mem_flat B S hS F hE

/-- A cartesian presheaf of modules on a slice of the affine étale site of `F` is a sheaf. -/
theorem isSheaf_of_cartesian_affineEtale_over
    (U : AffineEtale B S hS F)
    (M : PresheafOfModules.{max m (u + 1)}
      ((Over.forget U).op ⋙ (affineEtaleStructureSheaf B S hS F hF).obj ⋙
        forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m}
        (R := (Over.forget U).op ⋙ (affineEtaleStructureSheaf B S hS F hF).obj) M f)) :
    Presheaf.IsSheaf ((AffineEtale.topology B S hS F).over U) M.presheaf := by
  let L := AffineEtale.toScheme B S hS F
  have (X : Over U) : IsAffine ((Over.forget U ⋙ L).obj X) :=
    AffineEtale.isAffine_toScheme B S hS F X.left
  refine Stacks.PresheafOfModules.isSheaf_of_affine_flat_refinements.{u, u + 1, m, u + 1, u}
    (Over.forget U ⋙ L)
    ((Over.forget U).op ⋙ (affineEtaleStructureSheaf B S hS F hF).obj) ?_ M hM _ ?_
  · rw [affineEtaleStructurePresheaf_eq B S hS F hF]
    rfl
  · intro V T hT
    exact Stacks.Sites.exists_finite_flat_refinement_over L
      (AffineEtale.precoverage B S hS F)
      (affineEtale_covering_finite_flat B S hS F) U T hT

/-- A sheaf of modules on the affine étale site of `F` which has a global presentation on the
slice over `U` is cartesian over every morphism of that slice. -/
theorem isIso_restrictionBaseChange_over_of_hasGlobalPresentation
    (M : SheafOfModules.{max m (u + 1)} (affineEtaleRingSheaf B S hS F hF))
    (U : AffineEtale B S hS F) (hM : (M.over U).HasGlobalPresentation)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m}
      (R := (Over.forget U).op ⋙ (affineEtaleStructureSheaf B S hS F hF).obj)
      (M.over U).val f) := by
  apply Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_hasGlobalPresentation.{u + 1,
      u, u + 1, m}
    ((Over.forget U).op ⋙ (affineEtaleStructureSheaf B S hS F hF).obj)
    (Sheaf.over (affineEtaleRingSheaf B S hS F hF) U).property
    (fun N hN => isSheaf_of_cartesian_affineEtale_over B S hS F hF U N hN)
    (M.over U) hM f

/-- Being cartesian is local on a covering of the affine étale site of `F`: if the base object
has a finite covering on whose slices a sheaf of modules is cartesian, then it is cartesian over
every morphism into the base object. -/
theorem isIso_restrictionBaseChange_affineEtale_of_cover
    (M : PresheafOfModules.{max m (u + 1)}
      ((affineEtaleStructureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf)
    {V : AffineEtale B S hS F} {I : Type (u + 1)} [Finite I]
    (W : I → AffineEtale B S hS F) (gw : ∀ i, W i ⟶ V)
    (hcover : Sieve.ofArrows W gw ∈ AffineEtale.topology B S hS F V)
    (hcart : ∀ (i : I) {X Y : AffineEtale B S hS F} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m} M a.op))
    {U : AffineEtale B S hS F} (f : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m} M f.op) := by
  classical
  have hsT : Presieve.IsSheaf (AffineEtale.topology B S hS F)
      (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (AffineEtale.topology B S hS F)
      M.presheaf (forget AddCommGrpCat)).mp hs
  have hcoverU : Sieve.ofArrows (fun i => pullback f (gw i))
      (fun i => pullback.fst f (gw i)) ∈ AffineEtale.topology B S hS F U := by
    refine (AffineEtale.topology B S hS F).superset_covering ?_
      ((AffineEtale.topology B S hS F).pullback_stable f hcover)
    intro Z h hh
    obtain ⟨Y, g₁, g₂, ⟨i⟩, hg⟩ := hh
    have hmem := (Sieve.ofArrows (fun i => pullback f (gw i))
        (fun i => pullback.fst f (gw i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  have hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows W gw) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcover)
  have hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU)
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover M f W gw
    (flat_affineEtaleStructurePresheaf_map B S hS F hF f) hsfV hsfU
    (fun i => isPushout_affineEtaleStructurePresheaf B S hS F hF
      (IsPullback.of_hasPullback f (gw i)))
    (fun c => isPushout_affineEtaleStructurePresheaf B S hS F hF
      (IsPullback.of_hasPullback f _))
    (fun i => hcart i (pullback.snd f (gw i)) (𝟙 _) (pullback.snd f (gw i)) (by simp))
    (fun c => hcart c.1 (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1) ≫
      pullback.fst (gw c.1) (gw c.2)) (pullback.fst (gw c.1) (gw c.2))
      (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1)) rfl)

/-- A quasi-coherent sheaf of modules on the affine étale site of an algebraic space is
cartesian: each restriction map exhibits its target as a base change of its source. -/
@[stacks 0H04 "quasi-coherent implies cartesian"]
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{max m (u + 1)} (affineEtaleRingSheaf B S hS F hF))
    (hM : M.IsQuasicoherentOnSite)
    {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m} M.val f.op) := by
  classical
  obtain ⟨I, hI, W, g, hcover, hpres⟩ :=
    Stacks.SheafOfModules.exists_finite_globalPresentation_cover.{u + 1, u, u + 1, m}
      (AffineEtale.precoverage B S hS F)
      (fun P hP => (affineEtale_covering_finite_flat B S hS F P hP).1) M hM V
  have hcart (i : I) {X Y : (Over (W i))ᵒᵖ} (a : X ⟶ Y) :=
    isIso_restrictionBaseChange_over_of_hasGlobalPresentation B S hS F hF M (W i) (hpres i) a
  let _ := hI
  have hcart' : ∀ (i : I) {X Y : AffineEtale B S hS F} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, m} M.val a.op) := by
    intro i X Y x y a ha
    exact hcart i (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha))
  exact isIso_restrictionBaseChange_affineEtale_of_cover B S hS F hF M.val M.isSheaf W g hcover
    hcart' f

end AlgebraicGeometry.Space

end
