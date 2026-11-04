module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSupport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Pseudo-coherence and supports under the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. The functor `G : D(𝒪_{Λ X}) ⥤ D(𝒪_X)` induced by the
inverse of the equivalence of modules `AlgebraicGeometry.Space.relocalizeModulesEquivalence`
carries pseudo-coherent objects to pseudo-coherent objects, and an object supported on a subset
`Y` of `|Λ X|` to an object supported on the inverse image of `Y` in `|X|`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_relocalizeInverse_obj`: `G` preserves
  pseudo-coherence (Stacks 08FT).
* `AlgebraicGeometry.Space.cohomologySupportedOn_relocalizeInverse_obj`: `G` and supports
  (Stacks 08GF).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- The functor `D(𝒪_{Λ X}) ⥤ D(𝒪_X)` induced by the inverse of the relocalization of modules. -/
abbrev relocalizeInverse :
    DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) ⥤
      DerivedCategory (Modules.{u, u} B T hT X hX) :=
  (relocalizeModulesEquivalence B hT hS g X hX).inverse.mapDerivedCategory

/-- **The inverse relocalization preserves pseudo-coherence.** -/
theorem isPseudoCoherent_relocalizeInverse_obj
    (L : DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)))
    (hL : (smallEtaleRingedSite B S hS _
      (isAlgebraicSpace_relocalize' B hT hS g X hX)).IsPseudoCoherent L) :
    (smallEtaleRingedSite B T hT X hX).IsPseudoCoherent
      ((relocalizeInverse B hT hS g X hX).obj L) :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
    RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso
      (X := smallEtaleRingedSite B T hT X hX)
      (Y := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX))
      (SmallEtale.relocalize B hT hS g X hX)
      (hfun := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsContinuous
        (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)))
      (hinv := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).inverse.IsContinuous
        (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X)))
      (𝟙 _) (hρ := IsIso.id _) L m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hL m)

/-- **The inverse relocalization and supports.** If `L ∈ D(𝒪_{Λ X})` is supported on `Y ⊆ |Λ X|`,
then its image in `D(𝒪_X)` is supported on the inverse image of `Y` in `|X|`. -/
theorem cohomologySupportedOn_relocalizeInverse_obj
    (Y : Set (points B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)))
    (L : DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)))
    (hL : CohomologySupportedOn B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX) Y L) :
    CohomologySupportedOn B T hT X hX (pointsRelocalize B T S hT hS g X ⁻¹' Y)
      ((relocalizeInverse B hT hS g X hX).obj L) := by
  intro i
  refine (supportOfSheaf_eq_of_isoSheaf B T hT X hX ((SheafOfModules.toSheaf _).mapIso
    (((relocalizeModulesEquivalence B hT hS g X hX).inverse.mapDerivedCategoryHomologyFunctorIso
      i).app L))).trans_subset ?_
  exact (supportOfSheaf_relocalize B hT hS g hX _).le.trans (Set.preimage_mono (hL i))


/-- The relocalization of derived categories `ρ : D(𝒪_X) ≌ D(𝒪_{Λ X})`, with inverse
`AlgebraicGeometry.Space.relocalizeInverse`. -/
abbrev relocalizeInverseEquivalence :
    DerivedCategory (Modules.{u, u} B T hT X hX) ≌
      DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX)) :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence
    (relocalizeModulesEquivalence B hT hS g X hX).functor
    (relocalizeModulesEquivalence B hT hS g X hX).inverse
    (relocalizeModulesEquivalence B hT hS g X hX).unitIso
    (relocalizeModulesEquivalence B hT hS g X hX).counitIso

/-- **The relocalization of the derived structure sheaf is the derived structure sheaf**,
`ρ(𝒪_X[0]) ≅ 𝒪_{Λ X}[0]`: `ρ` is the derived pullback along the morphism of ringed topoi
`AlgebraicGeometry.Space.relocalizeRingedToposHom`. -/
def relocalizeDerivedFunctorUnitIso :
    (relocalizeDerivedFunctor B hT hS g X hX).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT ⟨X, hX⟩))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)) :=
  ((relocalizeDerivedPullbackIso B hT hS g X hX).app _).symm ≪≫
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
      (relocalizeRingedToposHom B hT hS g X hX)

/-- **The inverse relocalization of the derived structure sheaf is the derived structure
sheaf**, `G(𝒪_{Λ X}[0]) ≅ 𝒪_X[0]`. -/
def relocalizeInverseUnitIso :
    (relocalizeInverse B hT hS g X hX).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT ⟨X, hX⟩)) :=
  (relocalizeInverse B hT hS g X hX).mapIso (relocalizeDerivedFunctorUnitIso B hT hS g X hX).symm ≪≫
    ((relocalizeInverseEquivalence B hT hS g X hX).unitIso.app _).symm

variable {X' Y' : AlgebraicSpaces B T hT} (f : X' ⟶ Y')

/-- **The inverse relocalization commutes with derived direct images**:
`G_X ∘ R(Λ f)_* ≅ Rf_* ∘ G_Y`, read as `G_X ⋙ Rf_* ≅ R(Λ f)_* ⋙ G_Y`. -/
def relocalizeInversePushforwardIso :
    relocalizeInverse B hT hS g X'.1 X'.2 ⋙ derivedModulePushforward B T hT f ≅
      derivedModulePushforward B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeInverse B hT hS g Y'.1 Y'.2 :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (relocalizeInverseEquivalence B hT hS g Y'.1 Y'.2).unitIso ≪≫
    Functor.isoWhiskerLeft (relocalizeInverse B hT hS g X'.1 X'.2)
      (Functor.isoWhiskerRight (relocalizeDerivedPushforwardIso B hT hS g f)
        (relocalizeInverse B hT hS g Y'.1 Y'.2)) ≪≫
    Functor.isoWhiskerRight (relocalizeInverseEquivalence B hT hS g X'.1 X'.2).counitIso
      (derivedModulePushforward B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeInverse B hT hS g Y'.1 Y'.2) ≪≫
    Functor.leftUnitor _

/-- **The relocalization commutes with derived pullbacks**, `ρ_X ∘ Lf^* ≅ L(Λ f)^* ∘ ρ_Y`: both
are left adjoint to `G_X ⋙ Rf_* ≅ R(Λ f)_* ⋙ G_Y`. -/
def relocalizeDerivedPullbackCompIso :
    smallEtaleDerivedModulePullback B T hT f ⋙ relocalizeDerivedFunctor B hT hS g X'.1 X'.2 ≅
      relocalizeDerivedFunctor B hT hS g Y'.1 Y'.2 ⋙
        smallEtaleDerivedModulePullback B S hS (relocalizeHom B hT hS g f) :=
  Adjunction.leftAdjointUniq
    (((smallEtaleDerivedModuleAdjunction B T hT f).comp
      (relocalizeInverseEquivalence B hT hS g X'.1 X'.2).toAdjunction).ofNatIsoRight
        (relocalizeInversePushforwardIso B hT hS g f))
    ((relocalizeInverseEquivalence B hT hS g Y'.1 Y'.2).toAdjunction.comp
      (smallEtaleDerivedModuleAdjunction B S hS (relocalizeHom B hT hS g f)))

/-- **The inverse relocalization commutes with derived pullbacks**,
`G_Y ⋙ Lf^* ≅ L(Λ f)^* ⋙ G_X`. -/
def relocalizeInversePullbackIso :
    relocalizeInverse B hT hS g Y'.1 Y'.2 ⋙ smallEtaleDerivedModulePullback B T hT f ≅
      smallEtaleDerivedModulePullback B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeInverse B hT hS g X'.1 X'.2 :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (relocalizeInverseEquivalence B hT hS g X'.1 X'.2).unitIso ≪≫
    Functor.isoWhiskerLeft (relocalizeInverse B hT hS g Y'.1 Y'.2)
      (Functor.isoWhiskerRight (relocalizeDerivedPullbackCompIso B hT hS g f)
        (relocalizeInverse B hT hS g X'.1 X'.2)) ≪≫
    Functor.isoWhiskerRight (relocalizeInverseEquivalence B hT hS g Y'.1 Y'.2).counitIso
      (smallEtaleDerivedModulePullback B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeInverse B hT hS g X'.1 X'.2) ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Space

end
