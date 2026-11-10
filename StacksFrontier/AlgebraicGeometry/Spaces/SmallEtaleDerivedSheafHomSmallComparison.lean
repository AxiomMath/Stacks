module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceHeterogeneous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelSlices
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact

/-!
# The two spellings of `R𝓗om` and of `Rf_*` on the small étale site of an algebraic space

Two constructions of the derived internal Hom `R𝓗om(P, G)` on `D(𝒪_X)` for an algebraic space
`X` are in use:

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`, the derived internal Hom of the
  equi-universe model of the small étale ringed site read through the derived equivalence with
  the model;
* `AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor` of the small étale ringed site
  itself, built from the internal Hom complex at the module universe.

Likewise the derived direct image `Rf_*` is spelled both as
`AlgebraicGeometry.Space.derivedModulePushforward` and as the total right derived functor of
`AlgebraicGeometry.Space.modulePushforward`. This file identifies the two spellings of each, and
so the two spellings of the object `K = Rf_* R𝓗om(P, G)` of the proof of Stacks 08JY.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomIsoSmall`: the two derived internal Homs
  agree, at every pair of objects.
* `AlgebraicGeometry.Space.derivedModulePushforwardIsoTotalRightDerived`: the two derived direct
  images agree, as functors.
* `AlgebraicGeometry.Space.derivedModulePushforwardSheafHomIsoSmall`: the two spellings of
  `Rf_* R𝓗om(P, G)` agree.

## Implementation notes

The comparison of the derived internal Homs is the transport of the derived internal Hom along
the equivalence of the small étale site with its model,
`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomSmallIso`, followed by the unit of the
derived equivalence. The comparison of the direct images is the uniqueness of right derived
functors: both are right derived functors of `modulePushforward`.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat pointTopology isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For an equivalence `e : C' ≌ C` and a functor `R` on `Cᵒᵖ`, the image under `R` of the
opposite of the triangle identity `e.functor (η_A) ≫ ε_{e A} = 𝟙`. -/
theorem map_op_counit_comp_map_op_unit {C C' : Type*} [Category* C] [Category* C'] (e : C' ≌ C)
    {D : Type*} [Category* D] (R : Cᵒᵖ ⥤ D) (A : C'ᵒᵖ) :
    R.map ((NatTrans.op e.counit).app (e.functor.op.obj A)) ≫
        R.map (e.functor.op.map ((NatTrans.op e.unit).app A)) = 𝟙 _ := by
  rw [← R.map_comp, ← R.map_id]
  congr 1
  simp only [NatTrans.op_app, Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op]
  rw [← op_comp]
  exact congrArg Quiver.Hom.op (e.functor_unit_comp A.unop)

section SheafHom

variable (X : AlgebraicSpaces B S hS)

/-- The model equivalence `smallEtaleModelEquivalence`, with its source and target spelled as the
categories of the two ringed sites, so that instance search sees the categories of the sites. -/
def smallEtaleModelRingedSiteEquivalence :
    (smallEtaleModelRingedSite B S hS X.1 X.2).C ≌ (smallEtaleRingedSite B S hS X.1 X.2).C :=
  smallEtaleModelEquivalence B S hS X.1

/-- The functor of `smallEtaleModelRingedSiteEquivalence`, from the model site to the small étale
site, is continuous. -/
instance smallEtaleModelRingedSiteEquivalence_functor_isContinuous :
    (smallEtaleModelRingedSiteEquivalence B S hS X).functor.IsContinuous
      (smallEtaleModelRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).J :=
  smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2

/-- The inverse functor of `smallEtaleModelRingedSiteEquivalence`, from the small étale site to the
model site, is continuous. -/
instance smallEtaleModelRingedSiteEquivalence_inverse_isContinuous :
    (smallEtaleModelRingedSiteEquivalence B S hS X).inverse.IsContinuous
      (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleModelRingedSite B S hS X.1 X.2).J :=
  smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2

/-- The structure map `𝒪_model ⟶ e_* 𝒪_X` of the model equivalence: the identity, the model ring
being the direct image of the structure sheaf. -/
def smallEtaleModelRingSheafMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O ⟶
      ((smallEtaleModelRingedSiteEquivalence B S hS X).functor.sheafPushforwardContinuous
        RingCat.{u} (smallEtaleModelRingedSite B S hS X.1 X.2).J
          (smallEtaleRingedSite B S hS X.1 X.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  modelSharpInv B S hS X.1 X.2

/-- The structure map `𝒪_X ⟶ (e⁻¹)_* 𝒪_model` of the model equivalence, given by the counit. -/
def smallEtaleRingSheafModelMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O ⟶
      ((smallEtaleModelRingedSiteEquivalence B S hS X).inverse.sheafPushforwardContinuous
        RingCat.{u} (smallEtaleRingedSite B S hS X.1 X.2).J
          (smallEtaleModelRingedSite B S hS X.1 X.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  modelSharp B S hS X.1 X.2

/-- The first compatibility of the structure maps of the model equivalence
`smallEtaleModelEquivalence : model ≌ small étale site`, read with the identity of the model ring
as structure map `𝒪_model ⟶ e_* 𝒪_X` and the counit `modelSharp` as structure map
`𝒪_X ⟶ (e⁻¹)_* 𝒪_model`: these are the data of
`AlgebraicGeometry.Space.modulesEquivModelModules`. -/
theorem smallEtaleModel_compat₁ :
    Functor.whiskerRight (NatTrans.op (smallEtaleModelRingedSiteEquivalence B S hS X).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj =
      (smallEtaleRingSheafModelMap B S hS X).hom ≫
        (smallEtaleModelRingedSiteEquivalence B S hS X).inverse.op.whiskerLeft
          (smallEtaleModelRingSheafMap B S hS X).hom := by
  rfl

/-- The second compatibility of the structure maps of the model equivalence; see
`AlgebraicGeometry.Space.smallEtaleModel_compat₁`. -/
theorem smallEtaleModel_compat₂ :
    (smallEtaleModelRingSheafMap B S hS X).hom ≫
        (smallEtaleModelRingedSiteEquivalence B S hS X).functor.op.whiskerLeft
          (smallEtaleRingSheafModelMap B S hS X).hom ≫
        Functor.whiskerRight (NatTrans.op (smallEtaleModelRingedSiteEquivalence B S hS X).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleModelRingedSite B S hS X.1 X.2).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X.1 X.2).O).obj := by
  ext A : 2
  change 𝟙 _ ≫ (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map _ ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map _ =
    𝟙 _
  rw [Category.id_comp]
  exact map_op_counit_comp_map_op_unit (smallEtaleModelRingedSiteEquivalence B S hS X)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj A

/-- **The two derived internal Homs on an algebraic space agree.** For `P` and `G` in `D(𝒪_X)`,
the derived internal Hom `R𝓗om(P, G)` read through the equi-universe model
(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`) is the derived internal Hom of the small
étale ringed site at the module universe
(`AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor`): the transport of the latter to
the model is the derived internal Hom of the model
(`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomSmallIso`), and the derived equivalence
with the model brings it back. -/
def smallEtaleDerivedSheafHomIsoSmall
    (P G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj G ≅
      ((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS X.1 X.2)).obj
        (op P)).obj G :=
  haveI : PreservesFiniteLimits
      (SheafOfModules.pushforward.{u} (smallEtaleModelRingSheafMap B S hS X)) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforwardPushforwardEquivalence
      (smallEtaleModelRingedSiteEquivalence B S hS X) (smallEtaleModelRingSheafMap B S hS X)
      (smallEtaleRingSheafModelMap B S hS X) (smallEtaleModel_compat₁ B S hS X)
      (smallEtaleModel_compat₂ B S hS X)).functor)
  haveI : PreservesFiniteColimits
      (SheafOfModules.pushforward.{u} (smallEtaleModelRingSheafMap B S hS X)) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.pushforwardPushforwardEquivalence
      (smallEtaleModelRingedSiteEquivalence B S hS X) (smallEtaleModelRingSheafMap B S hS X)
      (smallEtaleRingSheafModelMap B S hS X) (smallEtaleModel_compat₁ B S hS X)
      (smallEtaleModel_compat₂ B S hS X)).functor)
  (smallEtaleModelDerivedEquivalence B S hS X).inverse.mapIso
      (RingedSite.siteEquivDerivedSheafHomSmallIso (X := smallEtaleRingedSite B S hS X.1 X.2)
        (Y := smallEtaleModelRingedSite B S hS X.1 X.2)
        (hDX := HasDerivedCategory.standard _) (hDY := HasDerivedCategory.standard _)
        (smallEtaleModelRingedSiteEquivalence B S hS X)
        (smallEtaleModelRingSheafMap B S hS X) (smallEtaleRingSheafModelMap B S hS X)
        (smallEtaleModel_compat₁ B S hS X) (smallEtaleModel_compat₂ B S hS X) P G).symm ≪≫
    ((smallEtaleModelDerivedEquivalence B S hS X).unitIso.app _).symm

end SheafHom

section Pushforward

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- **The two spellings of `Rf_* R𝓗om(P, G)` agree**: the derived direct image
`AlgebraicGeometry.Space.derivedModulePushforward` of the derived internal Hom
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` (the spelling of Stacks 08JQ) is the total
right derived functor of `AlgebraicGeometry.Space.modulePushforward` applied to the derived
internal Hom `AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor` of the small étale ringed
site (the spelling of Stacks 0DKK and 08JX). This is the object `K` of the proof of Stacks 08JY. -/
def derivedModulePushforwardSheafHomIsoSmall (f : X ⟶ Y)
    (P G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj G) ≅
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        (((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS X.1 X.2)).obj
          (op P)).obj G) :=
  (derivedModulePushforward B S hS f).mapIso (smallEtaleDerivedSheafHomIsoSmall B S hS X P G) ≪≫
    (derivedModulePushforwardIsoTotalRightDerived B S hS f).app _

end Pushforward

namespace HomSituation

open CoherentSituation

variable {B S hS} (s : HomSituation B S hS)

/-- **`K = Rf_* R𝓗om(P, 𝒢)` is perfect, in the spelling of Stacks 08JQ**
(`AlgebraicGeometry.Space.derivedModulePushforward` of
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`): this is
`AlgebraicGeometry.Space.HomSituation.isPerfect_derivedHomDirectImage` read through
`AlgebraicGeometry.Space.derivedModulePushforwardSheafHomIsoSmall`. -/
theorem isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) (hproper : HasProperSupportOver s.f s.G)
    (P : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2))
    (hP : (smallEtaleRingedSite B S hS s.X.1 s.X.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS s.base.1 s.base.2).IsPerfect
      ((derivedModulePushforward B S hS s.f).obj
        (((smallEtaleDerivedSheafHom B S hS s.X).obj (op P)).obj (DerivedCategory.Q.obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := s.isPerfect_derivedHomDirectImage hTop hB hf hfqs hGft hflat hproper P hP
  exact ⟨E, hE, ⟨e ≪≫ (derivedModulePushforwardSheafHomIsoSmall s.f P _).symm⟩⟩

/-- **`K = Rf_* R𝓗om(P, 𝒢)` is pseudo-coherent, in the spelling of Stacks 08JQ**; see
`isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom`. -/
theorem isPseudoCoherent_derivedModulePushforward_smallEtaleDerivedSheafHom
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) (hproper : HasProperSupportOver s.f s.G)
    (P : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2))
    (hP : (smallEtaleRingedSite B S hS s.X.1 s.X.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS s.base.1 s.base.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS s.f).obj
        (((smallEtaleDerivedSheafHom B S hS s.X).obj (op P)).obj (DerivedCategory.Q.obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))) := by
  obtain ⟨E, hE, ⟨e⟩⟩ :=
    s.isPseudoCoherent_derivedHomDirectImage hTop hB hf hfqs hGft hflat hproper P hP
  exact ⟨E, hE, ⟨e ≪≫ (derivedModulePushforwardSheafHomIsoSmall s.f P _).symm⟩⟩

/-- **`Rf_* R𝓗om(Q, 𝒢)` has no cohomology in negative degrees, in the spelling of Stacks 08JQ**,
for `Q` concentrated in degrees `≤ 0`: this is
`AlgebraicGeometry.Space.HomSituation.isGE_derivedHomDirectImage` read through
`AlgebraicGeometry.Space.derivedModulePushforwardSheafHomIsoSmall`. -/
theorem isGE_derivedModulePushforward_smallEtaleDerivedSheafHom
    (Q : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2)) [Q.IsLE 0] :
    ((derivedModulePushforward B S hS s.f).obj
        (((smallEtaleDerivedSheafHom B S hS s.X).obj (op Q)).obj (DerivedCategory.Q.obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))).IsGE 0 := by
  have h := s.isGE_derivedHomDirectImage Q
  exact ⟨(DerivedCategory.TStructure.t.ge 0).prop_of_iso
    (derivedModulePushforwardSheafHomIsoSmall s.f Q _).symm h.ge⟩

end HomSituation

end AlgebraicGeometry.Space

end
