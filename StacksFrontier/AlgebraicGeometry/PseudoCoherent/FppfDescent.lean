module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.OpenFlatSurjective
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.CyclesLift
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.RestrictionIsPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatSurjectiveDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksCore.Tactic.StacksAttribute

/-!
# `m`-pseudo-coherence descends along an fppf covering

Let `{f_i : X_i ⟶ X}` be an fppf covering of schemes, let `E` be an object of `D(𝒪_X)` and let
`m` be an integer. Stacks 09UF says that `E` is `m`-pseudo-coherent if and only if every derived
pullback `Lf_i^*E` is.

## Main results

* `Stacks.Cohomology.PseudoCoherence.FlatDescent.isPseudoCoherentFrom_iff_forall_fppf`: `E` is
  `m`-pseudo-coherent if and only if every `Lf_i^*E` is.
* `Stacks.Cohomology.PseudoCoherence.FlatDescent.isPseudoCoherentFrom_of_pullback_of_bounded`:
  the single-morphism statement, for an object whose derived pullback is bounded above.
* `AlgebraicGeometry.RingedSpace.derivedPullbackRestrictIso`: for a commuting square of a flat
  morphism of ringed spaces with two open immersions, the derived pullback of a restriction is the
  restriction of the derived pullback.
* `AlgebraicGeometry.RingedSpace.derivedPullbackHomologyIso`: along a flat morphism,
  `H^i(Lf^*E) ≅ f^*H^i(E)`.

## Implementation notes

The derived categories are the standard ones, fixed by a local instance of priority `2000`: the
locally small model is a global instance at the default priority.

## References

* [Stacks Project, Lemma 36.12.3 (Tag 09UF)](https://stacks.math.columbia.edu/tag/09UF)
* [Stacks Project, Lemma 20.47.3 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 20.47.9 (Tag 08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Lemma 35.7.2 (Tag 09UB)](https://stacks.math.columbia.edu/tag/09UB)
* [Stacks Project, Lemma 20.46.6 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace Stacks.Cohomology.HigherDirectImage
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u v

attribute [local instance 2000] _root_.HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u, u}}

/-! ### Restriction and pullback across a square of open immersions -/

/-- Degreewise pullback along a morphism between two open subspaces is additive. -/
public instance pullbackBetweenOpenSubspaces_additive {U : Opens X.carrier}
    {V : Opens Y.carrier} (g : restrictToOpen Y V ⟶ restrictToOpen X U) :
    (modulePullback g).Additive :=
  modulePullback_additive g

/-- Degreewise pullback along a morphism between two open subspaces, passed to homotopy
categories, has a left derived functor. -/
public instance hasLeftDerivedFunctor_pullbackOnHomotopy_openSubspaces {U : Opens X.carrier}
    {V : Opens Y.carrier} (g : restrictToOpen Y V ⟶ restrictToOpen X U) :
    (pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (restrictToOpen X U)))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy g

/-- Restriction to an open subspace followed by pullback along a morphism of open subspaces is
additive. -/
public theorem restrictCompPullback_additive (U : Opens X.carrier) (V : Opens Y.carrier)
    (g : restrictToOpen Y V ⟶ restrictToOpen X U) :
    (restrictModules.{u, u} X U ⋙ modulePullback g).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (restrictModules.{u, u} X U)
    (restrictModules_additive X U) _ _ _ (modulePullback g) (modulePullback_additive g)

/-- Pullback along a morphism of ringed spaces followed by restriction to an open subspace is
additive. -/
public theorem pullbackCompRestrict_additive (f : Y ⟶ X) (V : Opens Y.carrier) :
    (modulePullback f ⋙ restrictModules.{u, u} Y V).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
    (restrictModules.{u, u} Y V) (restrictModules_additive Y V)

/-- **Restriction commutes with pullback across a commuting square of open immersions.** Let
`f : Y ⟶ X` be a morphism of ringed spaces, let `U` be an open of `X`, let `V` be an open of `Y`
and let `g : Y|_V ⟶ X|_U` be a morphism with `g ≫ j_U = j_V ≫ f`. Then restricting an
`𝒪_X`-module to `U` and pulling it back along `g` agrees with pulling it back along `f` and
restricting to `V`, naturally in the module. -/
public def restrictPullbackSquareIso (f : Y ⟶ X) (U : Opens X.carrier) (V : Opens Y.carrier)
    (g : restrictToOpen Y V ⟶ restrictToOpen X U)
    (hsq : g ≫ openSubspaceInclusion X U = openSubspaceInclusion Y V ≫ f) :
    restrictModules.{u, u} X U ⋙ modulePullback g ≅
      modulePullback f ⋙ restrictModules.{u, u} Y V :=
  Functor.isoWhiskerRight (KFlatDerivedPullback.restrictModulesIsoPullback X U)
      (modulePullback g) ≪≫
    Stacks.DerivedPullback.Composition.modulePullbackComp g (openSubspaceInclusion X U) ≪≫
    eqToIso (congrArg (fun m : restrictToOpen Y V ⟶ X => modulePullback m) hsq) ≪≫
    (Stacks.DerivedPullback.Composition.modulePullbackComp
      (openSubspaceInclusion Y V) f).symm ≪≫
    Functor.isoWhiskerLeft (modulePullback f)
      (KFlatDerivedPullback.restrictModulesIsoPullback Y V).symm

/-- **Restriction commutes with pullback across a square of open immersions, degreewise on
complexes.** This is `AlgebraicGeometry.RingedSpace.restrictPullbackSquareIso` carried through
`CategoryTheory.NatIso.mapHomologicalComplex` and evaluated at the complex. -/
public def restrictComplexPullbackSquareIso (f : Y ⟶ X) (U : Opens X.carrier)
    (V : Opens Y.carrier) (g : restrictToOpen Y V ⟶ restrictToOpen X U)
    (hsq : g ≫ openSubspaceInclusion X U = openSubspaceInclusion Y V ≫ f)
    (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (restrictComplex K U) ≅
      restrictComplex
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V :=
  (@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (restrictCompPullback_additive U V g))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (pullbackCompRestrict_additive f V))
    (restrictPullbackSquareIso f U V g hsq) (ComplexShape.up ℤ)).app K

/-! ### The derived pullback along a flat morphism -/

/-- **Along a flat morphism the derived pullback of a complex is its degreewise pullback.** -/
public def derivedPullbackQIso (f : Y ⟶ X) (hf : AlgebraicGeometry.IsFlat f)
    (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  letI : PreservesFiniteLimits (modulePullback f) :=
    preservesFiniteLimits_modulePullback_of_isFlat f hf
  letI : PreservesFiniteColimits (modulePullback f) := preservesFiniteColimits_modulePullback f
  (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso f).app (DerivedCategory.Q.obj K) ≪≫
    ((modulePullback f).mapDerivedCategoryFactors).app K

/-- **Along a flat morphism the derived pullback commutes with the cohomology functors**:
`H^i(Lf^*E) ≅ f^*H^i(E)`. -/
public def derivedPullbackHomologyIso (f : Y ⟶ X) (hf : AlgebraicGeometry.IsFlat f) (i : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).obj ((derivedPullback f).obj E) ≅
      (modulePullback f).obj ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) :=
  letI : PreservesFiniteLimits (modulePullback f) :=
    preservesFiniteLimits_modulePullback_of_isFlat f hf
  letI : PreservesFiniteColimits (modulePullback f) := preservesFiniteColimits_modulePullback f
  (DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).mapIso
      ((AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso f).app E) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (modulePullback f) i).app E

/-- **The derived pullback of a derived restriction is the derived restriction of the derived
pullback**, across a commuting square of a flat morphism `f : Y ⟶ X` with the open immersions of
an open `U` of `X` and an open `V` of `Y`, the morphism `g : Y|_V ⟶ X|_U` being flat as well:
`Lg^*(E|_U) ≅ (Lf^*E)|_V`. -/
public def derivedPullbackRestrictIso (f : Y ⟶ X) (hf : AlgebraicGeometry.IsFlat f)
    (U : Opens X.carrier) (V : Opens Y.carrier)
    (g : restrictToOpen Y V ⟶ restrictToOpen X U) (hg : AlgebraicGeometry.IsFlat g)
    (hsq : g ≫ openSubspaceInclusion X U = openSubspaceInclusion Y V ≫ f)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (derivedPullback g).obj ((derivedRestrictModules X U).obj E) ≅
      (derivedRestrictModules Y V).obj ((derivedPullback f).obj E) :=
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  (derivedPullback g).mapIso ((derivedRestrictModules X U).mapIso e.symm) ≪≫
    (derivedPullback g).mapIso (derivedRestrictModulesObjQIso X U K) ≪≫
    derivedPullbackQIso g hg (restrictComplex K U) ≪≫
    DerivedCategory.Q.mapIso (restrictComplexPullbackSquareIso f U V g hsq K) ≪≫
    (derivedRestrictModulesObjQIso Y V
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (derivedRestrictModules Y V).mapIso (derivedPullbackQIso f hf K).symm ≪≫
    (derivedRestrictModules Y V).mapIso ((derivedPullback f).mapIso e)

end AlgebraicGeometry.RingedSpace

namespace Stacks.Cohomology.PseudoCoherence.FlatDescent

open AlgebraicGeometry.RingedSpace

variable {X Y : Scheme.{u}}

/-! ### A flat, surjective morphism of schemes locally of finite presentation -/

/-- A flat morphism of schemes is flat as a morphism of ringed spaces. -/
public theorem isFlat_toShHom (f : Y ⟶ X) [Flat f] :
    AlgebraicGeometry.IsFlat f.toLRSHom.toShHom := fun x => Flat.stalkMap f x

/-- The restriction `f|_U : f^{-1}(U) ⟶ U` of a surjective morphism of schemes to an open
subscheme of its target is surjective. -/
public instance surjective_morphismRestrict (f : Y ⟶ X) [Surjective f] (U : X.Opens) :
    Surjective (f ∣_ U) :=
  ⟨fun y => by
    obtain ⟨x, hx⟩ := f.surjective y.1
    exact ⟨⟨x, show f x ∈ U from hx ▸ y.2⟩,
      Subtype.ext ((morphismRestrict_base_coe f U _).trans hx)⟩⟩

/-- The morphism of ringed spaces underlying `f.resLE U V hVU`, followed by the inclusion of
`U`, is the inclusion of `V` followed by `f`. -/
public theorem resLE_square (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) :
    (f.resLE U V hVU).toLRSHom.toShHom ≫ openSubspaceInclusion X.toRingedSpace U =
      openSubspaceInclusion Y.toRingedSpace V ≫ f.toLRSHom.toShHom :=
  congrArg (fun h : V.toScheme ⟶ X => h.toLRSHom.toShHom) (f.resLE_comp_ι hVU)

/-- The morphism of ringed spaces underlying `f ∣_ U`, followed by the inclusion of `U`, is the
inclusion of `f⁻¹ U` followed by `f`. -/
public theorem morphismRestrict_square (f : Y ⟶ X) (U : X.Opens) :
    (f ∣_ U).toLRSHom.toShHom ≫ openSubspaceInclusion X.toRingedSpace U =
      openSubspaceInclusion Y.toRingedSpace (f ⁻¹ᵁ U) ≫ f.toLRSHom.toShHom :=
  congrArg (fun h : (f ⁻¹ᵁ U).toScheme ⟶ X => h.toLRSHom.toShHom) (morphismRestrict_ι f U)

/-- **Pullback along a flat surjection of schemes reflects zero objects.** -/
public theorem isZero_of_isZero_modulePullback (f : Y ⟶ X) [Flat f] [Surjective f]
    (G : OXMod.{u, u} X.toRingedSpace)
    (hG : IsZero ((modulePullback f.toLRSHom.toShHom).obj G)) : IsZero G :=
  Stacks.Cohomology.TorAmplitude.FlatDescent.isZero_of_isZero_modulePullback
    f.toLRSHom.toShHom f.surjective
    (fun x => Stacks.Cohomology.TorAmplitude.FlatDescent.isZero_of_isZero_stalkBaseChange
      f.toLRSHom.toShHom x (isFlat_toShHom f x)
      (LocallyRingedSpace.isLocalHomStalkMap f.toLRSHom x)
      (X.toLocallyRingedSpace.isLocalRing _) (Y.toLocallyRingedSpace.isLocalRing x))
    G hG

/-- **Finite type descends along a flat surjection of schemes locally of finite presentation.** -/
public theorem isFiniteType_of_isFiniteType_modulePullback (f : Y ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] (G : OXMod.{u, u} X.toRingedSpace)
    (hG : SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace)
      ((modulePullback f.toLRSHom.toShHom).obj G)) :
    SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace) G :=
  AlgebraicGeometry.isFiniteType_of_isFiniteType_modulePullback f.toLRSHom G
    f.isOpenMap f.surjective (isFlat_toShHom f) hG

/-- **The top cohomology sheaf of an object whose derived pullback is `m`-pseudo-coherent is of
finite type.** Let `f : Y ⟶ X` be flat, surjective and locally of finite presentation, let
`Lf^*E` be `m`-pseudo-coherent and let the cohomology of `E` vanish above a degree `b ≥ m`. Then
`H^b(E)` is an `𝒪_X`-module of finite type. -/
public theorem isFiniteType_homology (f : Y ⟶ X) [Flat f] [LocallyOfFinitePresentation f]
    [Surjective f] (m b : ℤ) (hmb : m ≤ b)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : IsPseudoCoherentFrom ((derivedPullback f.toLRSHom.toShHom).obj E) m)
    (hvanish : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E)) :
    SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) b).obj E) := by
  have hpull : SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) b).obj
        ((derivedPullback f.toLRSHom.toShHom).obj E)) :=
    isFiniteType_homology_of_isPseudoCoherentFrom
      ((derivedPullback f.toLRSHom.toShHom).obj E) b (hE.mono hmb) fun i hi =>
        IsZero.of_iso ((modulePullback f.toLRSHom.toShHom).map_isZero (hvanish i hi))
          (derivedPullbackHomologyIso f.toLRSHom.toShHom (isFlat_toShHom f) i E)
  have htgt : SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace)
      ((modulePullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) b).obj E)) :=
    SheafOfModules.IsFiniteType.of_iso
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace) hpull
      (derivedPullbackHomologyIso f.toLRSHom.toShHom (isFlat_toShHom f) b E)
  exact isFiniteType_of_isFiniteType_modulePullback f _ htgt

/-- An object of `D(𝒪_X)` with no cohomology above `p` and `H^p` of finite type is represented
by a complex that is `p`-pseudo-coherent. -/
private theorem exists_isPseudoCoherentComplexFrom_of_isFiniteType_homology
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (p : ℤ)
    (hv : ∀ j : ℤ, p < j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E))
    (hft : SheafOfModules.IsFiniteType
      (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) p).obj E)) :
    ∃ (K : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) (_ : DerivedCategory.Q.obj K ≅ E),
      IsPseudoCoherentComplexFrom K p := by
  set K := DerivedCategory.Q.objPreimage E
  have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  have eH : ∀ j : ℤ, K.homology j ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E := fun j =>
    (derivedHomologyIso K j).symm ≪≫
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).mapIso e
  exact ⟨K, e, isPseudoCoherentComplexFrom_of_isFiniteType_homology K p
    (fun j hj => IsZero.of_iso (hv j hj) (eH j))
    (SheafOfModules.IsFiniteType.of_iso
      (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace) hft (eH p).symm)⟩

/-! ### The descent along a single morphism -/

/-- If `f : Y ⟶ X` is flat, surjective and locally of finite presentation, `Lf^*E` is
`m`-pseudo-coherent and the cohomology of `E` vanishes above `m + k`, then `E` is
`m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_of_pullback_ind (k : ℕ) :
    ∀ (X Y : Scheme.{u}) (f : Y ⟶ X), Flat f → LocallyOfFinitePresentation f → Surjective f →
      ∀ (m : ℤ) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
        IsPseudoCoherentFrom ((derivedPullback f.toLRSHom.toShHom).obj E) m →
        (∀ j : ℤ, m + (k : ℤ) < j →
          IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E)) →
        IsPseudoCoherentFrom E m := by
  induction k with
  | zero =>
    intro X Y f hflat hlfp hsurj m E hE hvanish
    have := hflat; have := hlfp; have := hsurj
    have hv : ∀ j : ℤ, m < j →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E) :=
      fun j hj => hvanish j (by push_cast; omega)
    have hft := isFiniteType_homology f m m le_rfl E hE hv
    obtain ⟨K, e, hK⟩ := exists_isPseudoCoherentComplexFrom_of_isFiniteType_homology E m hv hft
    exact hK.isPseudoCoherentFrom_Q.ofIso e
  | succ k ih =>
    intro X Y f hflat hlfp hsurj m E hE hvanish
    have := hflat; have := hlfp; have := hsurj
    have hvp : ∀ j : ℤ, m + (k : ℤ) + 1 < j →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E) :=
      fun j hj => hvanish j (by push_cast; omega)
    have hft := isFiniteType_homology f m (m + (k : ℤ) + 1) (by omega) E hE hvp
    obtain ⟨K, e, hK⟩ :=
      exists_isPseudoCoherentComplexFrom_of_isFiniteType_homology E (m + (k : ℤ) + 1) hvp hft
    refine isPseudoCoherentFrom_of_local_restrict E m fun x => ?_
    obtain ⟨U, hxU, P, hP, α, hα, hαepi⟩ := hK x
    refine ⟨U, hxU, ?_⟩
    have hPpc : ∀ j : ℤ, IsPseudoCoherentFrom
        (X := X.toRingedSpace.restrict U.isOpenEmbedding) (DerivedCategory.Q.obj P) j :=
      fun j => (isPseudoCoherentComplexFrom_of_isStrictlyPerfect hP j).isPseudoCoherentFrom_Q
    have eE : DerivedCategory.Q.obj (restrictComplex K U) ≅
        (derivedRestrictModules X.toRingedSpace U).obj E :=
      (derivedRestrictModulesObjQIso X.toRingedSpace U K).symm ≪≫
        (derivedRestrictModules X.toRingedSpace U).mapIso e
    refine IsPseudoCoherentFrom.ofIso ?_ eE
    have h1 : IsPseudoCoherentFrom
        ((derivedRestrictModules Y.toRingedSpace (f ⁻¹ᵁ (U : X.Opens))).obj
          ((derivedPullback f.toLRSHom.toShHom).obj E)) m := by
      exact isPseudoCoherentFrom_derivedRestrictModules _ m hE _
    have h2 : IsPseudoCoherentFrom
        ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).obj
          ((derivedRestrictModules X.toRingedSpace U).obj E)) m := by
      exact h1.ofIso (derivedPullbackRestrictIso f.toLRSHom.toShHom (isFlat_toShHom f) U
        (f ⁻¹ᵁ (U : X.Opens)) (f ∣_ (U : X.Opens)).toLRSHom.toShHom
        (isFlat_toShHom (f ∣_ (U : X.Opens))) (morphismRestrict_square f U) E).symm
    have hLpc : IsPseudoCoherentFrom
        ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (restrictComplex K U))) m := by
      exact h2.ofIso ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).mapIso eE.symm)
    obtain ⟨Cn, β, γ, hT⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map α)
    have hiso : ∀ j : ℤ, m + (k : ℤ) + 1 < j →
        IsIso ((DerivedCategory.homologyFunctor
          (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) j).map
            (DerivedCategory.Q.map α)) := fun j hj =>
      CategoryTheory.isIso_homologyFunctor_map_Q_map α j (hα j hj)
    have hepi : Epi ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) (m + (k : ℤ) + 1)).map
          (DerivedCategory.Q.map α)) :=
      CategoryTheory.epi_homologyFunctor_map_Q_map α (m + (k : ℤ) + 1) hαepi
    have hCvanish : ∀ j : ℤ, m + (k : ℤ) + 1 ≤ j →
        IsZero ((DerivedCategory.homologyFunctor
          (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) j).obj Cn) := by
      exact isZero_homology_obj₃_of_distinguished (m + (k : ℤ) + 1) _ hT hiso hepi
    have hCpc : IsPseudoCoherentFrom
        ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).obj Cn) m := by
      exact isPseudoCoherentFrom_obj₃_of_distinguished m
        ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).mapTriangle.obj
          (Triangle.mk (DerivedCategory.Q.map α) β γ))
        ((derivedPullback (f ∣_ (U : X.Opens)).toLRSHom.toShHom).map_distinguished _ hT)
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
          (f ∣_ (U : X.Opens)).toLRSHom.toShHom (DerivedCategory.Q.obj P) (m + 1) (hPpc (m + 1)))
        hLpc
    have hCm : IsPseudoCoherentFrom (X := X.toRingedSpace.restrict U.isOpenEmbedding) Cn m := by
      exact ih (show X.Opens from U).toScheme (f ⁻¹ᵁ (U : X.Opens)).toScheme
        (f ∣_ (U : X.Opens)) inferInstance inferInstance inferInstance m Cn hCpc
        fun j hj => hCvanish j (by omega)
    exact isPseudoCoherentFrom_obj₂_of_distinguished m
      (Triangle.mk (DerivedCategory.Q.map α) β γ) hT (hPpc m) hCm

/-- **Descent of `m`-pseudo-coherence along a single flat surjection locally of finite
presentation, for an object with bounded above derived pullback.** -/
public theorem isPseudoCoherentFrom_of_pullback_of_bounded (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f] (m b : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : IsPseudoCoherentFrom ((derivedPullback f.toLRSHom.toShHom).obj E) m)
    (hb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) j).obj
        ((derivedPullback f.toLRSHom.toShHom).obj E))) :
    IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_pullback_ind (b - m).toNat X Y f ‹_› ‹_› ‹_› m E hE fun j hj => ?_
  refine isZero_of_isZero_modulePullback f _ ?_
  exact IsZero.of_iso (hb j (by have := Int.self_le_toNat (b - m); omega))
    (derivedPullbackHomologyIso f.toLRSHom.toShHom (isFlat_toShHom f) j E).symm

/-! ### fppf coverings -/

/-- The members of an fppf covering family form a flat precovering family. -/
private theorem ofArrows_mem_precoverage_flat {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X) :
    Presieve.ofArrows Y f ∈ Scheme.precoverage @Flat X := by
  rw [Scheme.fppfPrecoverage_eq_inf] at hf
  exact hf.1

/-- Every point of the target of an fppf covering family is in the image of one of its
members. -/
public theorem exists_preimage_of_mem_fppfPrecoverage {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X) (x : X) : ∃ i y, (f i) y = x := by
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp
    (ofArrows_mem_precoverage_flat Y f hf)).1 x

/-- Every member of an fppf covering family is flat. -/
public theorem flat_of_mem_fppfPrecoverage {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X) (i : I) : Flat (f i) := by
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp
    (ofArrows_mem_precoverage_flat Y f hf)).2 i

/-- Every member of an fppf covering family is locally of finite presentation. -/
public theorem locallyOfFinitePresentation_of_mem_fppfPrecoverage {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X) (i : I) :
    LocallyOfFinitePresentation (f i) := by
  have hlfp : Presieve.ofArrows Y f ∈ Scheme.precoverage @LocallyOfFinitePresentation X := by
    rw [Scheme.fppfPrecoverage_eq_inf] at hf
    exact hf.2
  exact ((Scheme.ofArrows_mem_precoverage_iff
    (P := @LocallyOfFinitePresentation)).mp hlfp).2 i

/-- Let `{f_i : X_i ⟶ X}` be an fppf covering of schemes, let `E` be an object of `D(𝒪_X)` and
let `m` be an integer. Then `E` is `m`-pseudo-coherent if and only if each `Lf_i^*E` is
`m`-pseudo-coherent. -/
@[stacks 09UF]
public theorem isPseudoCoherentFrom_iff_forall_fppf {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (m : ℤ) :
    IsPseudoCoherentFrom E m ↔
      ∀ i : I, IsPseudoCoherentFrom
        ((derivedPullback (f i).toLRSHom.toShHom).obj E) m := by
  refine ⟨fun hE i => KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback _ E m hE,
    fun hEi => isPseudoCoherentFrom_of_local_restrict E m fun x => ?_⟩
  obtain ⟨i, y, hy⟩ := exists_preimage_of_mem_fppfPrecoverage Y f hf x
  have hflat := flat_of_mem_fppfPrecoverage Y f hf i
  have hlfp := locallyOfFinitePresentation_of_mem_fppfPrecoverage Y f hf i
  obtain ⟨V, hyV, b, hb⟩ := exists_isZero_homology_gt_derivedRestrict
    ((derivedPullback (f i).toLRSHom.toShHom).obj E) m (hEi i) y
  refine ⟨⟨f i '' (V : Set (Y i)), (f i).isOpenMap _ V.isOpen⟩, ⟨y, hyV, hy⟩, ?_⟩
  set U : X.Opens := ⟨f i '' (V : Set (Y i)), (f i).isOpenMap _ V.isOpen⟩
  have hVU : (show (Y i).Opens from V) ≤ (f i) ⁻¹ᵁ U := fun z hz => ⟨z, hz, rfl⟩
  have hsurj : Surjective ((f i).resLE U (show (Y i).Opens from V) hVU) :=
    ⟨fun ⟨_, w, hw, hwz⟩ => ⟨⟨w, hw⟩, Subtype.ext (((f i).coe_resLE_apply hVU ⟨w, hw⟩).trans hwz)⟩⟩
  let e := derivedPullbackRestrictIso (f i).toLRSHom.toShHom (isFlat_toShHom (f i)) U V
    ((f i).resLE U (show (Y i).Opens from V) hVU).toLRSHom.toShHom
    (isFlat_toShHom _) (resLE_square (f i) U (show (Y i).Opens from V) hVU) E
  have hpc := (isPseudoCoherentFrom_derivedRestrictModules
    ((derivedPullback (f i).toLRSHom.toShHom).obj E) m (hEi i) V).ofIso e.symm
  have hbd := fun j (hj : b < j) => IsZero.of_iso (hb j hj)
    ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} ((Y i).toRingedSpace.restrict V.isOpenEmbedding)) j).mapIso e)
  exact isPseudoCoherentFrom_of_pullback_of_bounded
    ((f i).resLE U (show (Y i).Opens from V) hVU) m b
    ((derivedRestrictModules X.toRingedSpace U).obj E) hpc hbd

end Stacks.Cohomology.PseudoCoherence.FlatDescent

end
