module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.IsoBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PeriodicResolution
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.PseudoCoherentRelative.TildePseudoCoherent
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DJA (3) without a condition on `g` fails

Let `A` be a commutative ring with an element `e ≠ 0` such that `e² = 0` and whose annihilator is
`eA`, for example `A = ℤ/4` and `e = 2`; put `k = A/eA`. Take the cartesian square

```
Spec k --g--> Spec A
  |             |
  1             1
  v             v
Spec k --g--> Spec A
```

with `g` the closed immersion, `K = 𝒪_{Spec A}` (bounded below, quasi-coherent), `K' = L g^* K`
and `φ = id`, which satisfies condition (1) of Stacks 0DJ8, and the pseudo-coherent object
`E = P̃` where `P : ⋯ --e--> A --e--> A` is the periodic resolution of `k`. Then
`R𝓗om(E, K) ≅ E`, because `Hom^•(P, A)` is again a resolution of `k`, so the cohomology of
`L g^* R𝓗om(E, K)` in degree `-1` is `Tor_1^A(k, k) = k ≠ 0`; but `R𝓗om(L g^* E, K')` lies in
degrees `≥ 0`. Hence the comparison `L g^* R𝓗om(E, K) ⟶ R𝓗om(L g^* E, K')` is not an
isomorphism, and since the vertical arrows of the square are identities, condition (1) of
Stacks 0DJ8 fails for it.

Here `g` does not have finite Tor dimension: `Tor_i^A(k, k) = k` for every `i ≥ 0`. With `g` of
finite Tor dimension part (3) holds, as
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_hasTorAmplitude`.

## Main results

* `AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent`: the statement of
  Stacks 0DJA (3) with no condition on `g` is false.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeSheafHomComparison)
open Stacks.SheafOfModules (derivedSheafHom)
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace SheafHomPseudoCoherentCounterexample

open DualNumberLike

section Tilde

variable (R : CommRingCat.{u})

/-- The sheafification functor `M ↦ M̃` on `R`-modules preserves finite limits. -/
local instance : PreservesFiniteLimits (tilde.functor R) := tilde.preservesFiniteLimits R

/-- The cohomology of the sheafification of an object of `D(R)` is the sheafification of its
cohomology. -/
def homologyTildeIso (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      (tilde.functor R).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
  (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (tilde.functor R) n).app M

/-- Every cohomology sheaf of the sheafification of an object of `D(R)` is quasi-coherent. -/
theorem isQuasicoherent_homology_tilde (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M)).IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
    (homologyTildeIso R M n).symm inferInstance

/-- If the `n`-th cohomology sheaf of the sheafification of `M ∈ D(R)` vanishes, then so does the
`n`-th cohomology module of `M`. -/
theorem isZero_homology_of_isZero_homology_tilde (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((tilde.functor R).mapDerivedCategory.obj M))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
  IsZero.of_full_of_faithful_of_isZero (tilde.functor R) _ (h.of_iso (homologyTildeIso R M n).symm)

variable {R} {S : CommRingCat.{u}} (f : R ⟶ S)

/-- Derived pullback along `Spec f` of a sheafified object is the sheafification of the derived
base change. -/
def pullbackTildeIso (M : DerivedCategory (ModuleCat.{u} R)) :
    (derivedPullback (Spec.map f).toLRSHom.toShHom).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      (tilde.functor S).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj M) :=
  (StandardModel.affinePullbackComparison R S f).app M

end Tilde

section Objects

/-- Applying a functor preserving zero morphisms to a module placed in degree `0` gives a complex
strictly concentrated in degrees `≥ 0`. -/
private theorem isStrictlyGE_zero_map_single {R : CommRingCat.{u}} {D : Type*} [Category D]
    [Preadditive D] [HasZeroObject D] (F : ModuleCat.{u} R ⥤ D) [F.PreservesZeroMorphisms]
    (M : ModuleCat.{u} R) :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact F.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega))

variable {R : CommRingCat.{u}} {e : R} (he : e * e = 0)
  (hker : ∀ x : R, e * x = 0 → ∃ y, e * y = x)

/-- Every term of the periodic resolution `P` is a finite free `R`-module. -/
theorem isFiniteFree_P (i : ℤ) : StacksDraft.PseudoCoherence.IsFiniteFree ((P he hker).X i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, -(j : ℤ) = i := ⟨(-i).toNat, by omega⟩
    let l := (eX he hker i j hj).toLinearEquiv.symm
    exact ⟨Module.Finite.equiv l, Module.Free.of_equiv l⟩
  · have := ModuleCat.isZero_iff_subsingleton.1 ((P he hker).isZero_of_isStrictlyLE 0 i (by omega))
    exact ⟨inferInstance, inferInstance⟩

/-- The periodic resolution `P` is a pseudo-coherent object of `D(R)`. -/
theorem isPseudoCoherent_P :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj (P he hker)) :=
  ⟨P he hker, ⟨⟨0, inferInstance⟩, isFiniteFree_P he hker⟩, ⟨Iso.refl _⟩⟩

/-- The pseudo-coherent object `E = P̃` of `D(𝒪_{Spec R})`. -/
abbrev sheafE : DerivedCategory (Spec R).Modules :=
  (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj (P he hker))

/-- The structure sheaf `𝒪_{Spec R}`, as an object of `D(𝒪_{Spec R})`. -/
abbrev sheafK : DerivedCategory (Spec R).Modules :=
  (tilde.functor R).mapDerivedCategory.obj
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))

/-- The object `E = P̃` of `D(𝒪_{Spec R})` is pseudo-coherent. -/
theorem isPseudoCoherent_sheafE :
    RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) (sheafE he hker) := by
  obtain ⟨L, hL, ⟨i⟩⟩ :=
    Stacks.AffineTilde.isPseudoCoherent_tildeComplex (P he hker) (isPseudoCoherent_P he hker)
  let L' : CochainComplex (Spec R).Modules ℤ := L
  let i' : DerivedCategory.Q.obj L' ≅
      DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex (P he hker)) := i
  let j : DerivedCategory.Q.obj L' ≅ sheafE he hker :=
    i' ≪≫ ((tilde.functor R).mapDerivedCategoryFactors.app (P he hker)).symm
  exact ⟨L, hL, ⟨j⟩⟩

variable (R) in
/-- The object `sheafK` is represented by a complex of `𝒪_{Spec R}`-modules that is strictly
concentrated in degrees `≥ 0`. -/
theorem boundedBelow_sheafK :
    ∃ (L : CochainComplex (Spec R).Modules ℤ) (a : ℤ), L.IsStrictlyGE a ∧
      Nonempty (DerivedCategory.Q.obj L ≅ sheafK (R := R)) := by
  exact ⟨_, 0, isStrictlyGE_zero_map_single (tilde.functor R) (ModuleCat.of R R),
    ⟨((tilde.functor R).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).symm⟩⟩

end Objects

section Main

variable {R : CommRingCat.{u}} {e : R} (he : e * e = 0)
  (hker : ∀ x : R, e * x = 0 → ∃ y, e * y = x)

include he hker in
/-- **The statement of Stacks 0DJA (3) with no condition on `g` fails**, over any ring `R` with an
element `e` such that `e² = 0` and whose annihilator is `eR`, and any nonzero ring `S` over `R` in
which `e` vanishes: for the cartesian square with `g : Spec S ⟶ Spec R` and identities as vertical
arrows, `K = 𝒪_{Spec R}`, `K' = L g^* K`, `φ = id` and `E = P̃` for the periodic resolution `P`
of `R/eR`, condition (1) of Stacks 0DJ8 holds for `φ` but not for
`L g^* R𝓗om(E, K) ⟶ R𝓗om(L g^* E, K')`. -/
theorem not_pointwiseBaseChangeSheafHomOfPseudoCoherent_of_sq_eq_zero {S : CommRingCat.{u}}
    [Nontrivial S] (π : R ⟶ S) (hπ : π.hom e = 0) :
    ¬ (∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
      IsPullback g' f' f g →
      ∀ (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules)
        (K' : DerivedCategory X'.Modules)
        (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
        RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
        (∃ (L : CochainComplex X.Modules ℤ) (a : ℤ), L.IsStrictlyGE a ∧
          Nonempty (DerivedCategory.Q.obj L ≅ K)) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
        PointwiseBaseChangeIsIso f g f' g' w K K' φ →
        PointwiseBaseChangeIsIso f g f' g' w
          (((derivedSheafHom X.sheaf).obj (op E)).obj K)
          (((derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
          (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)) := by
  intro h
  let g : Spec S ⟶ Spec R := Spec.map π
  have hpb : IsPullback g (𝟙 _) (𝟙 _) g := IsPullback.of_id_snd
  let Lg := derivedPullback g.toLRSHom.toShHom
  let K' := Lg.obj (sheafK (R := R))
  have hKq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (sheafK (R := R))).IsQuasicoherent := fun n => isQuasicoherent_homology_tilde R _ n
  have hK'q : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec S).Modules n).obj
      K').IsQuasicoherent := fun n =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)
      ((DerivedCategory.homologyFunctor (Spec S).Modules n).mapIso (pullbackTildeIso π _)).symm
      (isQuasicoherent_homology_tilde S _ n)
  have hH : PointwiseBaseChangeIsIso (𝟙 _) g (𝟙 _) g hpb.w (sheafK (R := R)) K' (𝟙 _) :=
    fun x' n => isIso_baseChangeCohomologyMap_of_isIso hpb.w _ _ (𝟙 _) x' n
  have hC := h (𝟙 _) g (𝟙 _) g hpb hpb.w (sheafE he hker) (sheafK (R := R)) K' (𝟙 _)
    (isPseudoCoherent_sheafE he hker) (boundedBelow_sheafK R) hKq hK'q hH
  have hiso := isIso_of_isIso_baseChangeCohomologyMap_of_isIso hpb.w _ _ _ hC
  let T := totalDerivedExtensionScalars.{u, u, u} π.hom
  -- the target lies in degrees `≥ 0`
  have hGE : K'.IsGE 0 := by
    let L : CochainComplex (ModuleCat.{u} S) ℤ :=
      (ModuleCat.extendScalars π.hom).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
    have : L.IsStrictlyGE 0 :=
      isStrictlyGE_zero_map_single (ModuleCat.extendScalars π.hom) (ModuleCat.of R R)
    have hc : IsIso (T.comparison.app
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :=
      T.comparison_isIso_of_kFlat
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
        (CochainComplex.DerivedTensor.kFlat_single_of_flat (ModuleCat.of R R))
    let c : T.functor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        DerivedCategory.Q.obj L :=
      @asIso _ _ _ _ (T.comparison.app
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) hc
    have : (T.functor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso c.symm 0
    have := (tilde.functor S).isGE_obj_mapDerivedCategory
      (T.functor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) 0
      inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso (pullbackTildeIso π _).symm 0
  have hLE : (Lg.obj (sheafE he hker)).IsLE 0 := by
    have : (T.functor.obj (DerivedCategory.Q.obj (P he hker))).IsLE 0 :=
      T.maps_t_le (DerivedCategory.Q.obj (P he hker)) 0
    have := Stacks.Homology.isLE_mapDerivedCategory_obj (tilde.functor S)
      (T.functor.obj (DerivedCategory.Q.obj (P he hker))) 0
    exact DerivedCategory.TStructure.t.isLE_of_iso (pullbackTildeIso π _).symm 0
  have hT := Stacks.SheafOfModules.isGE_derivedSheafHom (Spec S).sheaf
    (Lg.obj (sheafE he hker)) K' 0 0 hLE hGE
  rw [sub_zero] at hT
  have hTz := DerivedCategory.isZero_of_isGE _ 0 (-1) (by norm_num) (hX := hT)
  -- the source has nonzero cohomology in degree `-1`
  have hplus : (DerivedCategory.TStructure.t).plus (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :=
    ⟨0, inferInstance⟩
  let eRHom : ((derivedSheafHom (Spec R).sheaf).obj (op (sheafE he hker))).obj (sheafK (R := R)) ≅
      sheafE he hker :=
    affinePseudoCoherentDerivedSheafHomIso R (DerivedCategory.Q.obj (P he hker))
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
      (isPseudoCoherent_P he hker) hplus ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso
      (StacksDraft.DerivedHom.projectiveHomComparison.iso (P he hker)
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) 0 ≪≫
        (resolutionIsoDual he hker).symm)
  have hc : IsIso (T.comparison.app (P he hker)) := T.comparison_isIso_of_projective (P he hker) 0
  let cP : T.functor.obj (DerivedCategory.Q.obj (P he hker)) ≅
      DerivedCategory.Q.obj (reducedResolution he hker π.hom) :=
    @asIso _ _ _ _ (T.comparison.app (P he hker)) hc
  let eSrc := Lg.mapIso eRHom ≪≫ pullbackTildeIso π _ ≪≫
    (tilde.functor S).mapDerivedCategory.mapIso cP
  have h1 : IsZero ((DerivedCategory.homologyFunctor (Spec S).Modules (-1)).obj
      ((tilde.functor S).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (reducedResolution he hker π.hom)))) :=
    hTz.of_iso ((DerivedCategory.homologyFunctor (Spec S).Modules (-1)).mapIso
      (eSrc.symm ≪≫ @asIso _ _ _ _ _ hiso))
  exact not_isZero_homology_reducedResolution he hker π.hom hπ
    ((isZero_homology_of_isZero_homology_tilde S _ (-1) h1).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) (-1)).app
        (reducedResolution he hker π.hom)).symm)

end Main

end SheafHomPseudoCoherentCounterexample

/-- The reduction `ℤ/4 ⟶ ℤ/2`, in an arbitrary universe. -/
def zmodFourReduction : ULift.{u} (ZMod 4) →+* ULift.{u} (ZMod 2) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).comp ULift.ringEquiv.toRingHom)

/-- The statement of part (3) of Stacks 0DJA, with the equivalent conditions of Stacks 0DJ8 read in
form (1) and `g` an arbitrary morphism, fails: for `A = ℤ/4`, the cartesian square with
`g : Spec ℤ/2 ⟶ Spec ℤ/4` the closed immersion and identities as vertical arrows,
`K = 𝒪_{Spec ℤ/4}`, `K' = L g^* K`, `φ = id`, and `E` the pseudo-coherent object attached to the
resolution `⋯ --2--> ℤ/4 --2--> ℤ/4` of `ℤ/2`, condition (1) of Stacks 0DJ8 holds for `φ` but
fails for `L g^* R𝓗om(E, K) ⟶ R𝓗om(L g^* E, K')`, whose source has cohomology
`Tor_1^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0` in degree `-1` while its target lies in degrees `≥ 0`. -/
@[stacks 0DJA "(3) as written is false: the statement of part (3), with no condition on g, fails \
by a counterexample over ℤ/4 with g : Spec ℤ/2 ⟶ Spec ℤ/4, K the structure sheaf and E the \
periodic resolution of ℤ/2"]
theorem not_pointwiseBaseChangeSheafHomOfPseudoCoherent :
    ¬ (∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
      IsPullback g' f' f g →
      ∀ (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules)
        (K' : DerivedCategory X'.Modules)
        (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
        RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
        (∃ (L : CochainComplex X.Modules ℤ) (a : ℤ), L.IsStrictlyGE a ∧
          Nonempty (DerivedCategory.Q.obj L ≅ K)) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
        PointwiseBaseChangeIsIso f g f' g' w K K' φ →
        PointwiseBaseChangeIsIso f g f' g' w
          (((derivedSheafHom X.sheaf).obj (op E)).obj K)
          (((derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
          (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)) := by
  have he : (ULift.up 2 : ULift.{u} (ZMod 4)) * ULift.up 2 = 0 := ULift.down_injective (by decide)
  have hker : ∀ x : ULift.{u} (ZMod 4), ULift.up 2 * x = 0 → ∃ y, ULift.up 2 * y = x := by
    rintro ⟨x⟩ hx
    have key : ∀ y : ZMod 4, 2 * y = 0 → ∃ z, 2 * z = y := by decide
    obtain ⟨z, hz⟩ := key x (congrArg ULift.down hx)
    exact ⟨ULift.up z, ULift.down_injective hz⟩
  open SheafHomPseudoCoherentCounterexample in
  exact not_pointwiseBaseChangeSheafHomOfPseudoCoherent_of_sq_eq_zero
    (R := CommRingCat.of (ULift.{u} (ZMod 4))) he hker
    (S := CommRingCat.of (ULift.{u} (ZMod 2))) (CommRingCat.ofHom zmodFourReduction)
    (ULift.down_injective (by decide))

end AlgebraicGeometry
