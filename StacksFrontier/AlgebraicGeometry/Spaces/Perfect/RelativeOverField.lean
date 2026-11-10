module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Relative perfectness over a field, for algebraic spaces

Let `k` be a field, let `X` be an algebraic space locally of finite presentation over `k`, and
let `f : X ⟶ Spec k`. A bounded pseudo-coherent object of `D(𝒪_X)` is perfect relative to
`Spec k`. Every fibre of `f⁻¹𝒪_{Spec k}` on the small étale site of `X` is a field, and every
sheaf of modules on the inverse-image ringed site and on each of its slices is flat.

## Main results

* `StacksDraft.FieldFibre.isFlat_of_isField_fibers`: on a ringed site whose structure-sheaf
  fibres at a conservative family of points are fields, every sheaf of modules is flat.
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePointOver`: the localizations of
  the geometric points are a conservative family of points of a slice of the small étale site.
* `AlgebraicGeometry.Space.isField_presheafFiber_inverseImage`: every fibre of `f⁻¹𝒪_{Spec k}`
  is a field.
* `AlgebraicGeometry.Space.isFlat_of_fieldSpace_over`: every sheaf of modules on a slice of the
  inverse-image ringed site of a morphism to `Spec k` is flat.
* `AlgebraicGeometry.Space.isFlat_toFieldSpace`: an algebraic space over the spectrum of a field
  is flat over it.
* `AlgebraicGeometry.Space.isPerfectRelativeTo_of_isBounded_of_isPseudoCoherent`: a bounded
  pseudo-coherent object of `D(𝒪_X)` is perfect relative to `Spec k`.

## References

* [Stacks Project, Tag 0DKP](https://stacks.math.columbia.edu/tag/0DKP)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u d e

namespace StacksDraft.FieldFibre

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- On a ringed site whose structure-sheaf fibres at a conservative family of points are
fields, every sheaf of modules is flat. -/
@[sga "4 XVII 5.5.25.4" "more general"]
theorem isFlat_of_isField_fibers (O : Sheaf J CommRingCat.{w}) {t : Type*}
    (p : t → J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (hfield : ∀ i, IsField (((p i).presheafFiber (A := CommRingCat.{w})).obj O.obj))
    (F : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    AlgebraicGeometry.SheafOfModules.IsFlat F := by
  refine Stacks.isFlat_of_forall_isFlatModuleStalk O F p hp (fun i => ?_)
  let : Field (((p i).presheafFiber (A := CommRingCat.{w})).obj O.obj) := (hfield i).toField
  let : Module.Free (((p i).presheafFiber (A := CommRingCat.{w})).obj O.obj)
      (Stacks.moduleStalk (p i) O F) := Module.Free.of_divisionRing _ _
  exact Module.Flat.of_free

end StacksDraft.FieldFibre

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The localizations of the geometric points are a conservative family of points of a slice
of the small étale site.** -/
theorem isConservativeFamilyOfPoints_etaleSitePointOver
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj
        (fun ψ : Σ x : GeometricPoint B S hS F,
            (etaleSitePoint B S hS F x hF).fiber.obj V =>
          (etaleSitePoint B S hS F ψ.1 hF).over ψ.2)) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro Y T hT
  obtain ⟨Y, g, rfl⟩ := Over.mk_surjective Y
  obtain ⟨T, rfl⟩ := (Sieve.overEquiv (Over.mk g)).symm.surjective T
  rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
  refine smallEtale_sieve_of_pointwise_covering B S hS F Y T (fun z => ?_)
  obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS F Y z
  have hmem := ObjectProperty.ofObj_apply
    (fun ψ : Σ y : GeometricPoint B S hS F, (etaleSitePoint B S hS F y hF).fiber.obj V =>
      (etaleSitePoint B S hS F ψ.1 hF).over ψ.2)
    ⟨x, (etaleSitePoint B S hS F x hF).fiber.map g p⟩
  obtain ⟨W, h, hh, w, hw⟩ := hT ⟨_, hmem⟩
    ⟨p, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mpr rfl⟩
  refine ⟨W.left, h.left, (Sieve.overEquiv_symm_iff T h).1 hh,
    (BigFppfOver.toScheme B S hS).map w.val.val z', ?_⟩
  have hm : w.val.val ≫ (SmallEtale.toOver B S hS F).map h.left = p.val :=
    congrArg Subtype.val (congrArg Subtype.val hw)
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hm]
  exact hz

variable {X : AlgebraicSpaces B S hS} (k : Type u) [Field k]
  (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)

/-- **Every fibre of `f⁻¹𝒪_{Spec k}` is a field.** For a morphism `f : X ⟶ Spec k` of algebraic
spaces, the fibre at a geometric point `x` of `X` of the inverse image of the structure sheaf of
`Spec k` is a field. -/
theorem isField_presheafFiber_inverseImage (f : X ⟶ fieldSpace B hS hk b)
    (x : GeometricPoint B S hS X.1) :
    IsField (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (inverseImageRingedSite B S hS f).O.obj) := by
  have h1 : IsField ((((etaleSitePoint B S hS (fieldSpace B hS hk b).1
      (geometricPointMap f.hom x) (fieldSpace B hS hk b).2)).presheafFiber
        (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS (fieldSpace B hS hk b)).O.obj) :=
    MulEquiv.isField (isField_etaleLocalRing_fieldSpace B hS hk b _)
      (pointStalkRingEquiv B S hS (fieldSpace B hS hk b)
        (geometricPointMap f.hom x)).toMulEquiv
  exact MulEquiv.isField h1
    (((smallEtaleInverseImageFiberRingIso B S hS f x).app
      (smallEtaleRingedTopos B S hS (fieldSpace B hS hk b)).O
        ).commRingCatIsoToRingEquiv).symm.toMulEquiv

variable (f : X ⟶ fieldSpace B hS hk b)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

omit [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Over a field every sheaf of modules on every slice of the inverse-image ringed site is
flat.** -/
theorem isFlat_of_fieldSpace_over (V : (inverseImageRingedSite B S hS f).C)
    (M : RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over V)) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (O := ((inverseImageRingedSite B S hS f).over V).O) M := by
  refine StacksDraft.FieldFibre.isFlat_of_isField_fibers
    ((inverseImageRingedSite B S hS f).over V).O
    (fun ψ : Σ x : GeometricPoint B S hS X.1,
        (etaleSitePoint B S hS X.1 x X.2).fiber.obj V =>
      (etaleSitePoint B S hS X.1 ψ.1 X.2).over ψ.2)
    (isConservativeFamilyOfPoints_etaleSitePointOver B S hS X.2 V) (fun ψ => ?_) M
  exact MulEquiv.isField (isField_presheafFiber_inverseImage B S hS k hk b f ψ.1)
    ((((CategoryTheory.GrothendieckTopology.Point.presheafFiberOverIso
      (etaleSitePoint B S hS X.1 ψ.1 X.2) ψ.2 CommRingCat.{u}).app
        (inverseImageRingedSite B S hS f).O.obj)).commRingCatIsoToRingEquiv).toMulEquiv

omit [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over U) AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **An algebraic space over the spectrum of a field is flat over it.** -/
theorem isFlat_toFieldSpace : IsFlat B S hS f.hom := by
  obtain ⟨U, a, ⟨haSurj, haEtale⟩⟩ := X.2.exists_atlas
  let V : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
  let h : U ⟶ V := yoneda.preimage (a ≫ f.hom)
  let T := BigFppfOver.toScheme B S hS
  let _ : Subsingleton (T.obj V) := by change Subsingleton (Spec (.of k)); infer_instance
  let _ : IsIntegral (T.obj V) := by change IsIntegral (Spec (.of k)); infer_instance
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@Flat.{u}) Flat.isEtaleLocalOnSourceAndTarget X.2
    (isAlgebraicSpace_yoneda B S hS V) f.hom).2
  refine ⟨U, V, a, 𝟙 _, h, haEtale, ?_, haSurj, by simp [h], by infer_instance⟩
  change (MorphismProperty.inverseImage (@Etale.{u}) T).relative yoneda (𝟙 (yoneda.obj V))
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 (yoneda.obj V)), ?_⟩
  intro A C g fst snd hsquare
  let _ : IsIso (yoneda.map snd) := hsquare.isIso_snd_of_isIso
  let _ : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact (inferInstance : Etale (T.map snd))

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
    [∀ U : (inverseImageRingedSite B S hS f).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

omit [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Let `k` be a field and let `X` be an algebraic space locally of finite presentation over
`k`. A bounded pseudo-coherent object of `D(𝒪_X)` is perfect relative to `Spec k`, the flatness
of `X ⟶ Spec k` being `isFlat_toFieldSpace`. -/
@[stacks 0DKP "bounded pseudo-coherent objects are perfect relative to a field"]
theorem isPerfectRelativeTo_of_isBounded_of_isPseudoCoherent
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hpc : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hbdd : DerivedCategoryB.IsBounded E) :
    IsPerfectRelativeTo B S hS f (isFlat_toFieldSpace B S hS k hk b f) hlfp T E := by
  refine ⟨hpc, Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_forall
    T _ (fun V => ?_)⟩
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hbdd
  have _ : E.IsGE lo := (DerivedCategory.isGE_iff E lo).2 hlo
  have _ : E.IsLE hi := (DerivedCategory.isLE_iff E hi).2 hhi
  obtain ⟨K, hKGE, hKLE, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE E lo hi
  let G := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
    (inverseImageRingedSite B S hS f).O) V
  let : Limits.PreservesFiniteLimits G :=
    RingedSite.sliceRestrictionPreservesFiniteLimits (inverseImageRingedSite B S hS f) V
  let : Limits.PreservesFiniteColimits G :=
    RingedSite.sliceRestrictionPreservesFiniteColimits (inverseImageRingedSite B S hS f) V
  let : HasDerivedCategory.{e} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (inverseImageRingedSite B S hS f).O).over V)) :=
    inferInstanceAs (HasDerivedCategory.{e}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over V)))
  have e' : DerivedCategory.Q.obj
      (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (derivedScalarRestriction B S hS f).obj E :=
    ((derivedScalarRestrictionFactors B S hS f).app K).symm ≪≫
      (derivedScalarRestriction B S hS f).mapIso eK.symm
  refine ⟨lo, hi, Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative
    (T V) _ lo hi
    ((inverseImageRingedSite B S hS f).restrictComplex
      (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V)
    (fun i => isFlat_of_fieldSpace_over B S hS k hk b f V _) (fun i hi' => ?_) ?_⟩
  · refine G.map_isZero
      ((scalarRestriction B S hS f).map_isZero ?_)
    rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi' : i < lo ∨ hi < i) with
      hlt | hgt
    · exact K.isZero_of_isStrictlyGE lo i hlt
    · exact K.isZero_of_isStrictlyLE hi i hgt
  · exact (G.mapDerivedCategoryFactors.app _).symm ≪≫ G.mapDerivedCategory.mapIso e'

end AlgebraicGeometry.Space

end
