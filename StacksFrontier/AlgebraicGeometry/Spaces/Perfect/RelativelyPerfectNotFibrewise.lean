module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FaithfullyFlatLocalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverFieldCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StalkOfPerfect
public import StacksFrontier.Homology.Perfect.Local
import StacksCore.Tactic.StacksAttribute

/-!
# Relative perfectness over a field is not perfectness on the fibres, for algebraic spaces

Let `k` be a field and let `X` be an algebraic space of finite presentation over `k`. By Stacks
0DKP, `AlgebraicGeometry.Space.isRelativelyPerfect_iff_derivedCategoryBBounded`, the `k`-perfect
objects of `D(𝒪_X)` are exactly the objects of `D^b_Coh(𝒪_X)`. The base being a point, the only
fibre of `X ⟶ Spec k` is `X` itself, so the closing sentence of that example — relative
perfectness does **not** mean perfectness on the fibres — says that some bounded complex with
coherent cohomology on such an `X` is not a perfect object of `D(𝒪_X)`.

This file exhibits one on the algebraic space `Spec k[ε]` of the dual numbers: the residue field
of `k[ε]`, made a module on the small étale site and placed in degree zero. It is coherent, hence
`k`-perfect; and it is not perfect, because its derived stalk at a geometric point `x̄` would be
perfect (`AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_moduleStalk_of_isPerfect`), that
stalk is the residue field base changed to the étale local ring `𝒪_{x̄}`
(`AlgebraicGeometry.Space.representedAffineAssociatedModuleStalkIso`), `𝒪_{x̄}` is faithfully flat
over `k[ε]`, perfectness descends along faithfully flat maps (Stacks 068T), and the residue field
of `k[ε]` is not a perfect module
(`AlgebraicGeometry.not_isPerfectModule_residueField_dualNumber`).

## Main definitions

* `AlgebraicGeometry.Space.dualNumberSpace` and `AlgebraicGeometry.Space.dualNumberSpaceMap`:
  `Spec k[ε]` as an algebraic space over `S`, with its structure morphism to `Spec k`.
* `AlgebraicGeometry.Space.dualNumberResidueModule`: the residue field of `k[ε]` as a module on
  the small étale site of `Spec k[ε]`, and `AlgebraicGeometry.Space.dualNumberResidueComplex` the
  same placed in degree zero.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_dualNumberSpaceMap`: `Spec k[ε]` is of finite
  presentation over `k`.
* `AlgebraicGeometry.Space.isCoherentOnSite_dualNumberResidueModule`: the residue module is
  coherent.
* `AlgebraicGeometry.Space.faithfullyFlat_dualNumberStalkRingHom`: the stalk ring of `Spec k[ε]`
  at a geometric point is faithfully flat over `k[ε]`.
* `AlgebraicGeometry.Space.isRelativelyPerfect_dualNumberResidueComplex_and_not_isPerfect`: the
  witness, in one statement — the residue complex of `Spec k[ε]` is `k`-perfect and is not
  perfect.

## Implementation notes

The derived categories of modules over the stalk ring and over `k[ε]` are taken to be the
standard ones, `HasDerivedCategory.standard`, in the proof of non-perfectness, because that is
where Stacks 068T and the non-perfectness of the residue field of `k[ε]` are stated; each spelling
of the stalk ring that occurs is given that instance locally. The derived category of
`𝒪_{Spec k[ε]}`-modules is arbitrary.

The containment of `Spec k[ε]` in the big fppf site follows from that of `Spec k`, the dual numbers
having the cardinality of `k × k` (`AlgebraicGeometry.Space.contains_spec_dualNumber`).

## References

* [Stacks Project, Tag 0DKP](https://stacks.math.columbia.edu/tag/0DKP)
* [Stacks Project, Tag 068T](https://stacks.math.columbia.edu/tag/068T)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d e

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)

/-- The spectrum of the dual numbers over `k` lies in every big fppf site containing `Spec k`:
the dual numbers have the cardinality of `k × k`. -/
theorem contains_spec_dualNumber (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of (DualNumber k))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk (by
    change Cardinal.mk (k × k) ≤ _
    rw [Cardinal.mk_prod, Cardinal.lift_id]
    exact (Cardinal.mul_le_max _ _).trans (by simp [le_total]))

/-- `Spec k[ε]`, over `S` through `Spec k`, as an object of the big fppf site. -/
def dualNumberOver : BigFppfOver B S hS :=
  Over.mk (⟨dualNumberStructureMap k ≫ b⟩ :
    B.obj (contains_spec_dualNumber B k hk) ⟶ B.obj hS)

/-- `Spec k[ε]` as an algebraic space over `S`. -/
def dualNumberSpace : AlgebraicSpaces B S hS := schemeSpace (dualNumberOver B S hS k hk b)

/-- The structure morphism `Spec k[ε] ⟶ Spec k`, of algebraic spaces over `S`. -/
def dualNumberSpaceMap : dualNumberSpace B S hS k hk b ⟶ fieldSpace B hS hk b :=
  schemeSpaceMap
    (Over.homMk (⟨dualNumberStructureMap k⟩ : B.obj (contains_spec_dualNumber B k hk) ⟶ B.obj hk)
      rfl)

/-- The scheme underlying `dualNumberOver` is `Spec k[ε]` itself. -/
def dualNumberSchemeIso :
    (BigFppfOver.toScheme B S hS).obj (dualNumberOver B S hS k hk b) ≅
      Spec (CommRingCat.of (DualNumber k)) :=
  Iso.refl _

/-- The residue field of `k[ε]`, as a module on the small étale site of `Spec k[ε]`: the module
associated with the quasi-coherent module `k̃` on `Spec k[ε]`. -/
def dualNumberResidueModule :
    Modules.{u, u} B S hS (dualNumberSpace B S hS k hk b).1 (dualNumberSpace B S hS k hk b).2 :=
  (representedAssociatedModule B S hS (dualNumberOver B S hS k hk b)
      (isAlgebraicSpace_yoneda B S hS _)).obj
    ((Scheme.Modules.restrictFunctor (dualNumberSchemeIso B S hS k hk b).hom).obj
      ((tilde.functor (CommRingCat.of (DualNumber k))).obj
        (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k)))))

/-- `Spec k[ε]` is locally Noetherian, as an algebraic space. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_dualNumberSpace :
    HasEtaleLocalProperty B S hS (dualNumberSpace B S hS k hk b).1
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_of_representable B S hS _ _ (dualNumberOver B S hS k hk b) (Iso.refl _)
    (by change IsLocallyNoetherian (Spec (CommRingCat.of (DualNumber k))); infer_instance)

/-- **The residue module of `Spec k[ε]` is coherent.** It is quasi-coherent, being associated
with a quasi-coherent module, and of finite type, being a quotient of the structure sheaf; on a
locally Noetherian algebraic space that is coherence (Stacks 07UB). -/
theorem isCoherentOnSite_dualNumberResidueModule :
    SheafOfModules.IsCoherentOnSite (dualNumberResidueModule B S hS k hk b) := by
  have := Fact.mk (show HasEtaleLocalProperty B S hS (yoneda.obj (dualNumberOver B S hS k hk b))
    (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) from
      hasEtaleLocalProperty_isLocallyNoetherian_dualNumberSpace B S hS k hk b)
  let A := CommRingCat.of (DualNumber k)
  let F := tilde.functor A ⋙
    Scheme.Modules.restrictFunctor (dualNumberSchemeIso B S hS k hk b).hom ⋙
    representedAssociatedModule B S hS (dualNumberOver B S hS k hk b)
      (isAlgebraicSpace_yoneda B S hS _)
  let π₀ : ModuleCat.of A A ⟶ ModuleCat.of A (IsLocalRing.ResidueField (DualNumber k)) :=
    ModuleCat.ofHom (Algebra.linearMap A (IsLocalRing.ResidueField (DualNumber k)))
  have : Epi π₀ := (ModuleCat.epi_iff_surjective _).2 IsLocalRing.residue_surjective
  have : Epi (F.map π₀) := inferInstance
  let π := (representedAffineUnitIso B S hS (dualNumberOver B S hS k hk b) A
    (dualNumberSchemeIso B S hS k hk b)).inv ≫ F.map π₀
  have : Epi (representedAffineUnitIso B S hS (dualNumberOver B S hS k hk b) A
      (dualNumberSchemeIso B S hS k hk b)).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have : Epi π := epi_comp _ _
  have hunit := (isCoherent_structureSheaf B S hS (yoneda.obj (dualNumberOver B S hS k hk b))
    (isAlgebraicSpace_yoneda B S hS _)).toIsCoherentOnSite
  have hft := Stacks.SheafOfModules.isFiniteType_of_locallySurjective π.val
    (@Stacks.SheafOfModules.exists_cover_preimage_of_epi _ _ _
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj (dualNumberOver B S hS k hk b))
          (isAlgebraicSpace_yoneda B S hS _)).O) _ _ _ _ π this) hunit.isFiniteType
  exact ((isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).2
    ⟨isQuasicoherentOnSite_representedAssociatedModule B S hS _ _ _ inferInstance,
      hft⟩).toIsCoherentOnSite

/-- `Spec k[ε] ⟶ Spec k` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_dualNumberSpaceMap :
    IsLocallyOfFinitePresentation B S hS (dualNumberSpaceMap B S hS k hk b).hom :=
  isLocallyOfFinitePresentation_yoneda_map B S hS _
    (inferInstanceAs (LocallyOfFinitePresentation (dualNumberStructureMap k)))

/-- **The stalk ring of `Spec k[ε]` at a geometric point is faithfully flat over `k[ε]`.** Read in
the étale local ring, the map `k[ε] → 𝒪_{x̄}` is the germ map to the local ring of `Spec k[ε]`
at the image of `x̄`, a localization, followed by the faithfully flat comparison of that local
ring with its strict henselization (Stacks 04KF); and it is local, every non-unit of `k[ε]`
being nilpotent. -/
theorem faithfullyFlat_dualNumberStalkRingHom
    (x : GeometricPoint B S hS (yoneda.obj (dualNumberOver B S hS k hk b))) :
    (representedAffineStalkRingHom B S hS (dualNumberOver B S hS k hk b) x
      (CommRingCat.of (DualNumber k)) (dualNumberSchemeIso B S hS k hk b)).FaithfullyFlat := by
  let U := dualNumberOver B S hS k hk b
  let hU := isAlgebraicSpace_yoneda B S hS U
  let V := selfNeighborhood B S hS U x
  let φ := representedAffineStalkRingHom B S hS U x (CommRingCat.of (DualNumber k))
    (dualNumberSchemeIso B S hS k hk b)
  let e := pointStalkRingEquiv B S hS ⟨yoneda.obj U, hU⟩ x
  let c := chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) hU V
  let T := (BigFppfOver.toScheme B S hS).obj U
  have : IsAffine T := by change IsAffine (Spec (CommRingCat.of (DualNumber k))); infer_instance
  let pt : (⊤ : T.Opens) := ⟨chartPoint B S hS (yoneda.obj U) V, trivial⟩
  let := TopCat.Presheaf.algebra_section_stalk T.presheaf pt
  have hloc := (isAffineOpen_top T).isLocalization_stalk pt
  let g : Γ(T, ⊤) →+* T.presheaf.stalk (chartPoint B S hS (yoneda.obj U) V) :=
    (T.presheaf.germ ⊤ (chartPoint B S hS (yoneda.obj U) V) trivial).hom
  have hg : g.Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (@IsLocalization.flat _ _ _ _ _ _ hloc)
  let γ : DualNumber k →+* Γ(T, ⊤) :=
    (dualNumberSchemeIso B S hS k hk b).hom.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
  have : IsIso (dualNumberSchemeIso B S hS k hk b).hom.appTop := by
    change IsIso (𝟙 _)
    infer_instance
  have hγ : Function.Bijective γ :=
    (ConcreteCategory.bijective_of_isIso (dualNumberSchemeIso B S hS k hk b).hom.appTop).comp
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv)
  have hcomp : e.toRingHom.comp φ = c.comp (g.comp γ) := by
    refine RingHom.ext fun a => ?_
    exact (pointStalkRingEquiv_representedAffineStalkRingHom B S hS U x _ _ a).trans
      (chartLocalRingToEtaleLocalRing_germ B S hS (yoneda.obj U) hU V _).symm
  have hφ : φ = e.symm.toRingHom.comp (c.comp (g.comp γ)) := by
    rw [← hcomp]
    exact RingHom.ext fun a => (e.symm_apply_apply (φ a)).symm
  have hflat : φ.Flat := by
    rw [hφ]
    exact ((RingHom.Flat.of_bijective hγ).comp hg |>.comp
      (flat_chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) hU V)).comp
      (RingHom.Flat.of_bijective e.symm.bijective)
  have : IsLocalRing (geometricStalkRing B S hS (X := ⟨yoneda.obj U, hU⟩) x) :=
    have := isLocalRing_etaleLocalRing B S hS _ hU x
    e.symm.isLocalRing
  have : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hfst : TrivSqZeroExt.fst (show DualNumber k from a) = 0 := by
      by_contra h0
      exact hna (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h0))
    have hsq : (show DualNumber k from a) * (show DualNumber k from a) = 0 := by
      have ha' : (show DualNumber k from a) = TrivSqZeroExt.inr
          (TrivSqZeroExt.snd (show DualNumber k from a)) := TrivSqZeroExt.ext hfst rfl
      rw [ha', TrivSqZeroExt.inr_mul_inr]
    have h0 : φ a * φ a = 0 := by rw [← map_mul]; exact (congrArg φ hsq).trans (map_zero φ)
    exact (ha.mul ha).ne_zero h0
  exact RingHom.Flat.faithfullyFlat_of_isLocalHom hflat


/-- `Spec k[ε]` is of finite presentation over `k`, as an algebraic space. -/
theorem isFinitePresentation_dualNumberSpaceMap :
    IsFinitePresentation B S hS (dualNumberSpaceMap B S hS k hk b).hom :=
  isFinitePresentation_yoneda_map B S hS _
    (show FinitePresentation (dualNumberStructureMap k) from
      ⟨inferInstance, inferInstance, inferInstance⟩)

section Derived

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS (dualNumberSpace B S hS k hk b).1
  (dualNumberSpace B S hS k hk b).2)]

/-- **The residue field of `k[ε]`, sheafified on the small étale site of `Spec k[ε]` and placed in
degree zero.** -/
abbrev dualNumberResidueComplex :
    DerivedCategory (Modules.{u, u} B S hS (dualNumberSpace B S hS k hk b).1
      (dualNumberSpace B S hS k hk b).2) :=
  (DerivedCategory.singleFunctor _ 0).obj (dualNumberResidueModule B S hS k hk b)

/-- The residue complex of `Spec k[ε]` is bounded: it is concentrated in degree zero. -/
theorem isBounded_dualNumberResidueComplex :
    DerivedCategoryB.IsBounded (dualNumberResidueComplex B S hS k hk b) :=
  ⟨⟨0, fun n hn => DerivedCategory.isZero_of_isGE _ 0 n hn⟩,
    ⟨0, fun n hn => DerivedCategory.isZero_of_isLE _ 0 n hn⟩⟩

/-- The residue complex of `Spec k[ε]` is pseudo-coherent: it is a coherent module in a single
degree, on a locally Noetherian algebraic space. -/
theorem isPseudoCoherent_dualNumberResidueComplex :
    (smallEtaleRingedSite B S hS (dualNumberSpace B S hS k hk b).1
      (dualNumberSpace B S hS k hk b).2).IsPseudoCoherent
        (dualNumberResidueComplex B S hS k hk b) := by
  let M := dualNumberResidueModule B S hS k hk b
  let K := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero (K.homology i) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M i hi
  refine ⟨K, isPseudoCoherentComplex_of_isCoherentOnSite_homology B S hS _ _
    (hasEtaleLocalProperty_isLocallyNoetherian_dualNumberSpace B S hS k hk b) K
    ⟨0, fun i hi => hz i (by omega)⟩ (fun i => ?_),
    ⟨((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (HomologicalComplex.singleObjHomologySelfIso _ _ _).symm
      (isCoherentOnSite_dualNumberResidueModule B S hS k hk b)
  · exact Stacks.SheafOfModules.isCoherentOnSite_zero (hz i hi)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

/-- The modules over the inverse image of the structure sheaf of `Spec k` form an abelian
category. -/
noncomputable local instance (priority := high) dualNumberInverseImageModules_abelian :
    Abelian (RingedSite.Modules.{u + 1, u, u}
      (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b))) :=
  SheafOfModules.instAbelian _

/-- The modules over each slice of the inverse image of the structure sheaf of `Spec k` form an
abelian category. -/
noncomputable local instance (priority := high) dualNumberInverseImageModulesOver_abelian
    (U : (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).C) :
    Abelian (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).over U)) :=
  SheafOfModules.instAbelian _

variable [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u}
    (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)))]
  [∀ U : (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).C,
    HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).over U))]

/-- **The residue complex of `Spec k[ε]` is `k`-perfect.** -/
theorem isRelativelyPerfect_dualNumberResidueComplex :
    IsRelativelyPerfect B S hS (dualNumberSpaceMap B S hS k hk b)
      (isFlat_toFieldSpace B S hS k hk b _)
      (isLocallyOfFinitePresentation_dualNumberSpaceMap B S hS k hk b)
      (dualNumberResidueComplex B S hS k hk b) :=
  isRelativelyPerfect_of_isBounded_of_isPseudoCoherent B S hS k hk b _ _ _
    (isPseudoCoherent_dualNumberResidueComplex B S hS k hk b)
    (isBounded_dualNumberResidueComplex B S hS k hk b)

attribute [local instance] _root_.Stacks.hasSheafCompose_forget₂_commRingCat

omit [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u}
    (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)))]
  [∀ U : (inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).C,
    HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (dualNumberSpaceMap B S hS k hk b)).over U))] in
/-- **The residue complex of `Spec k[ε]` is not perfect.** Its derived stalk at a geometric
point `x̄` is perfect if it is
(`AlgebraicGeometry.RingedSite.isPerfect_derivedModuleFiber_of_isPerfect`),
and that stalk is the residue field of `k[ε]` base changed to `𝒪_{x̄}`
(`AlgebraicGeometry.Space.representedAffineAssociatedModuleStalkIso`); since `𝒪_{x̄}` is
faithfully flat over `k[ε]`, perfectness descends (Stacks 068T), and the residue field of `k[ε]`
is not a perfect module. -/
theorem not_isPerfect_dualNumberResidueComplex :
    ¬ (smallEtaleRingedSite B S hS (dualNumberSpace B S hS k hk b).1
      (dualNumberSpace B S hS k hk b).2).IsPerfect (dualNumberResidueComplex B S hS k hk b) := by
  intro hE
  obtain ⟨x, -, -, -⟩ := exists_geo_lift_at_chart_point B S hS
    (yoneda.obj (dualNumberOver B S hS k hk b)) (selfChart B S hS (dualNumberOver B S hS k hk b))
    (show Spec (CommRingCat.of (DualNumber k)) from IsLocalRing.closedPoint (DualNumber k))
  let φ := representedAffineStalkRingHom B S hS (dualNumberOver B S hS k hk b) x
    (CommRingCat.of (DualNumber k)) (dualNumberSchemeIso B S hS k hk b)
  let M := ModuleCat.of (CommRingCat.of (DualNumber k)) (IsLocalRing.ResidueField (DualNumber k))
  let : HasDerivedCategory (ModuleCat.{u}
      (((etaleSitePoint B S hS (dualNumberSpace B S hS k hk b).1 x
        (dualNumberSpace B S hS k hk b).2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedSite B S hS (dualNumberSpace B S hS k hk b).1
            (dualNumberSpace B S hS k hk b).2).O.obj)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u}
      (((etaleSitePoint B S hS (yoneda.obj (dualNumberOver B S hS k hk b)) x
        (isAlgebraicSpace_yoneda B S hS _)).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj (dualNumberOver B S hS k hk b),
            isAlgebraicSpace_yoneda B S hS _⟩).O.obj)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS
      (X := ⟨yoneda.obj (dualNumberOver B S hS k hk b), isAlgebraicSpace_yoneda B S hS _⟩) x)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} (CommRingCat.of (DualNumber k))) :=
    HasDerivedCategory.standard _
  have hP := RingedSite.isPerfect_singleFunctor_moduleStalk_of_isPerfect
    (hR := HasDerivedCategory.standard _)
    (etaleSitePoint B S hS (dualNumberSpace B S hS k hk b).1 x (dualNumberSpace B S hS k hk b).2)
    _ hE
  let e := (DerivedCategory.singleFunctor _ 0).mapIso
        ((representedAffineAssociatedModuleStalkIso B S hS (dualNumberOver B S hS k hk b) x
          (CommRingCat.of (DualNumber k)) (dualNumberSchemeIso B S hS k hk b)).app M) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} φ) (ComplexShape.up ℤ) 0).app M).symm
  have hK := StacksDraft.Perfect.isPerfect_of_faithfullyFlat_baseChange.{u, u, u} φ
    (faithfullyFlat_dualNumberStalkRingHom B S hS k hk b x) _
    (StacksDraft.Perfect.isPerfect_of_iso e.symm hP)
  exact not_isPerfectModule_residueField_dualNumber k
    (StacksDraft.Perfect.isPerfect_of_iso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) hK)

/-- **Stacks 0DKP, the closing warning.** Over a field, relative perfectness is not perfectness
on the fibres: on the algebraic space `Spec k[ε]` — which is of finite presentation over `k`
(`AlgebraicGeometry.Space.isFinitePresentation_dualNumberSpaceMap`), and whose only fibre over
`Spec k` is itself — the residue field of the dual numbers, placed in degree zero, is `k`-perfect
and is not a perfect object of `D(𝒪_{Spec k[ε]})`. -/
@[stacks 0DKP "relative perfectness over a field is not perfectness on the fibres"]
theorem isRelativelyPerfect_dualNumberResidueComplex_and_not_isPerfect :
    IsRelativelyPerfect B S hS (dualNumberSpaceMap B S hS k hk b)
        (isFlat_toFieldSpace B S hS k hk b _)
        (isLocallyOfFinitePresentation_dualNumberSpaceMap B S hS k hk b)
        (dualNumberResidueComplex B S hS k hk b) ∧
      ¬ (smallEtaleRingedSite B S hS (dualNumberSpace B S hS k hk b).1
        (dualNumberSpace B S hS k hk b).2).IsPerfect (dualNumberResidueComplex B S hS k hk b) :=
  ⟨isRelativelyPerfect_dualNumberResidueComplex B S hS k hk b,
    not_isPerfect_dualNumberResidueComplex B S hS k hk b⟩

end Derived


end AlgebraicGeometry.Space

end
