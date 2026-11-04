module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatProperSupportSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeSupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallDerivedHomBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow

/-!
# The object `K = Rf_* RSheafHom(P, 𝒢)` of the proof of Stacks 08JY

In Situation 08JT, let the base `B` be Noetherian, `f : X ⟶ B` locally of finite type and
quasi-separated, and `𝒢` a quasi-coherent `𝒪_X`-module of finite type, flat over `B`, with
support proper over `B`.  For every perfect object `P` of `D(𝒪_X)` the object
`K = Rf_* RSheafHom(P, 𝒢)` of `D(𝒪_B)` is perfect, by Stacks 0DKK, hence pseudo-coherent.  This
is the object to which the proof of Stacks 08JY applies Stacks 08JX.

## Main results

* `AlgebraicGeometry.Space.HomSituation.isPerfect_derivedHomDirectImage`
* `AlgebraicGeometry.Space.HomSituation.isPseudoCoherent_derivedHomDirectImage`

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space.HomSituation

open CoherentSituation

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat pointTopology isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)

/-- **`K = Rf_* RSheafHom(P, 𝒢)` is perfect** (Stacks 08JY, by Stacks 0DKK): the base is
Noetherian, `f` is locally of finite type and quasi-separated, `P` is perfect, and `𝒢` is
coherent — quasi-coherent of finite type on the locally Noetherian space `X` — flat over the base
with support proper over it. -/
theorem isPerfect_derivedHomDirectImage (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) (hproper : HasProperSupportOver s.f s.G)
    (P : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2))
    (hP : (smallEtaleRingedSite B S hS s.X.1 s.X.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS s.base.1 s.base.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS s.f)).obj
        (((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS s.X.1 s.X.2)).obj
          (op P)).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))) := by
  have : Fact (HasEtaleLocalProperty B S hS s.X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS s.X.2 s.base.2 s.f.hom hf hB.2.2⟩
  have := s.quasicoherent_G
  have hGc : IsCoherent B S hS s.X.1 s.X.2 s.G :=
    (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS s.X.1 s.X.2 s.G).2
      ⟨inferInstance, Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite s.G hGft⟩
  obtain ⟨hp, hcl, hpr⟩ := hproper
  exact isPerfect_derivedModulePushforward_derivedSheafHom B S hS hTop s.f hf hfqs hB P hP _
    (flatProperSupportComplex_single B S hS s.f hf s.G hGc hflat hcl hpr)

/-- **`K = Rf_* RSheafHom(P, 𝒢)` is pseudo-coherent**, being perfect. -/
theorem isPseudoCoherent_derivedHomDirectImage (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) (hproper : HasProperSupportOver s.f s.G)
    (P : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2))
    (hP : (smallEtaleRingedSite B S hS s.X.1 s.X.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS s.base.1 s.base.2).IsPseudoCoherent
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS s.f)).obj
        (((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS s.X.1 s.X.2)).obj
          (op P)).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))) :=
  RingedSite.isPseudoCoherent_of_isPerfect_univ _
    (s.isPerfect_derivedHomDirectImage hTop hB hf hfqs hGft hflat hproper P hP)

/-- **`Rf_* RSheafHom(Q, 𝒢)` has no cohomology in negative degrees** for `Q` concentrated in
degrees `≤ 0` (the last sentence of the proof of Stacks 08JY): `RSheafHom(Q, 𝒢)` has no
cohomology in negative degrees, as `𝒢` sits in degree zero, and `Rf_*` is left t-exact. -/
theorem isGE_derivedHomDirectImage
    (Q : DerivedCategory (Modules.{u, u} B S hS s.X.1 s.X.2)) [Q.IsLE 0] :
    ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS s.f)).obj
        (((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS s.X.1 s.X.2)).obj
          (op Q)).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)))).IsGE 0 := by
  have h := RingedSite.isGE_derivedSheafHomSmall (smallEtaleRingedSite B S hS s.X.1 s.X.2) Q
    (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj s.G)) 0 0
  rw [sub_zero] at h
  exact isGE_derivedModulePushforward_obj B S hS s.f _ 0 h

end AlgebraicGeometry.Space.HomSituation

end
