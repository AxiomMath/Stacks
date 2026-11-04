module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlatSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# The canonical map of Tag 08I3 at a strictly perfect source

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be a strictly perfect
complex of `𝒪_Y`-modules.  For every object `M` of `D(𝒪_Y)` the canonical map

`Lh^* R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)`

of Tag 08I3 is an isomorphism.

## Main results

* `isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect`: for a strictly perfect complex `E`
  and any `M`, the canonical map `Lh^* R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)` is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf
  TopCat.Presheaf.IsSheaf

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- A direct summand of a finite free `𝒪_Z`-module is a retract of `𝒪_Z^{⊕r}` for some `r`. -/
theorem isFiniteFreeSummand_of_isDirectSummandOfFiniteFree (Z : RingedSpace.{u, u})
    {A : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z}
    (hA : StrictlyPerfect.IsDirectSummandOfFiniteFree A) :
    AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
      (AlgebraicGeometry.RingedSpace.ringedSite Z) A := by
  obtain ⟨n, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract A).1 hA
  exact AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free
    (AlgebraicGeometry.RingedSpace.ringedSite Z) (ULift.{u} (Fin n))
    (ρ.trans (StrictlyPerfect.finiteFreeIsoFree Z n).retract)

variable {X Y : RingedSpace.{u, u}}

/-- The comparison map `homComplexComparison` is invertible at a strictly perfect source. -/
private theorem isIso_homComplexComparison_of_isStrictlyPerfect (Z : RingedSpace.{u, u})
    (E F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hE : StrictlyPerfect.IsStrictlyPerfect E) : IsIso (homComplexComparison Z E F) :=
  AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso
    (Stacks.SheafOfModules.ringedSite Z.sheaf)
    (RingedSite.derivedInternalHomOfBifunctor (Stacks.SheafOfModules.ringedSite Z.sheaf))
    E F hE.bounded fun i =>
      isFiniteFreeSummand_of_isDirectSummandOfFiniteFree Z (hE.directSummand i)

/-- For a strictly perfect complex `E` and a K-flat complex `F` of `𝒪_Y`-modules, the canonical
map `Lh^* R𝓗om(E, F) ⟶ R𝓗om(Lh^*E, Lh^*F)` of Tag 08I3 is an isomorphism. -/
theorem isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect_of_kFlat (h : X ⟶ Y)
    (E F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hE : StrictlyPerfect.IsStrictlyPerfect E)
    (hF : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y F) :
    IsIso (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)) := by
  have hterm (i : ℤ) : AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
      (AlgebraicGeometry.RingedSpace.ringedSite Y) (E.X i) :=
    isFiniteFreeSummand_of_isDirectSummandOfFiniteFree Y (hE.directSummand i)
  have hpE := Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback h E hE
  have hkE := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect E hE
  have := isIso_homComplexComparison_of_isStrictlyPerfect Y E F hE
  have := isIso_homComplexComparison_of_isStrictlyPerfect X ((pullbackComplex h).obj E)
    ((pullbackComplex h).obj F) hpE
  have : IsIso (pullbackHomComplexMapSite h E F) :=
    isIso_pullbackHomComplexMap_of_isFiniteFreeSummand h E hE.bounded hterm F
  exact isIso_derivedPullbackSheafHomMap_of_models h E F hkE hF
    (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional h E hkE)
    (AlgebraicGeometry.RingedSite.isKFlat_sheafHomComplex_of_isKFlat
      (Stacks.SheafOfModules.ringedSite Y.sheaf) E F hE.bounded hterm hF)

/-- Invertibility transported across a commutative square whose other three sides are
isomorphisms. -/
private lemma isIso_of_square {C : Type*} [Category C] {a b c d : C} (l : a ≅ b) (φ : a ⟶ c)
    (r : c ≅ d) (φ' : b ⟶ d) (hφ : IsIso φ) (hsq : l.hom ≫ φ' = φ ≫ r.hom) : IsIso φ' := by
  rw [show φ' = l.inv ≫ φ ≫ r.hom by rw [← hsq, Iso.inv_hom_id_assoc]]
  infer_instance

/-- **The canonical map of Tag 08I3 is natural in its target variable.** -/
theorem derivedPullbackSheafHomMap_naturality_target (h : X ⟶ Y)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {M M' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (k : M ⟶ M') :
    (derivedPullbackFunctor h).map (((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).obj
        (op K)).map k) ≫ derivedPullbackSheafHomMap h K M' =
      derivedPullbackSheafHomMap h K M ≫
        ((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (op ((derivedPullbackFunctor h).obj K))).map ((derivedPullbackFunctor h).map k) :=
  Transpose.homComparison_naturality_target (derivedPullbackFunctor h)
    (AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite X.sheaf))
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X) (tensorHomBijection Y)
    (tensorHomBijection X) (pullbackTensorIso h) (tensorHomEquivNaturalLeft_ringedSpace Y)
    (curriedTargetNatural_ringedSpace Y) (tensorHomEquivNaturalLeft_ringedSpace X)
    (curriedTargetNatural_ringedSpace X) K k

/-- The canonical map of Tag 08I3 at `(K, M)` is invertible as soon as it is at `(K, M')` for
some `M'` isomorphic to `M`. -/
theorem isIso_derivedPullbackSheafHomMap_of_iso_target (h : X ⟶ Y)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {M M' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (k : M ≅ M') [hM : IsIso (derivedPullbackSheafHomMap h K M)] :
    IsIso (derivedPullbackSheafHomMap h K M') :=
  isIso_of_square
    ((derivedPullbackFunctor h).mapIso
      (((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).obj (op K)).mapIso k))
    (derivedPullbackSheafHomMap h K M)
    (((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
      (op ((derivedPullbackFunctor h).obj K))).mapIso ((derivedPullbackFunctor h).mapIso k))
    _ hM (derivedPullbackSheafHomMap_naturality_target h K k.hom)

/-- **Tag 08I3 at a strictly perfect source.**  For a morphism of ringed spaces
`h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, a strictly perfect complex `E` of `𝒪_Y`-modules and any object `M`
of `D(𝒪_Y)`, the canonical map `Lh^* R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)` is an isomorphism. -/
theorem isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect (h : X ⟶ Y)
    (E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hE : StrictlyPerfect.IsStrictlyPerfect E)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj E) M) := by
  obtain ⟨F, p, hF, -, hq, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Y
      (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have := isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect_of_kFlat h E F hE hF
  exact isIso_derivedPullbackSheafHomMap_of_iso_target h _
    (asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso M)

end Stacks.Cohomology.DerivedInternalHomPullback

end
