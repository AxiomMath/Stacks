module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedDualSystems
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedPushforwardDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Quot.PerfectDualIsoOfFieldFibres
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectHomWindow

/-!
# Stacks 0DKY from its steps

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces with `Y`
quasi-compact and quasi-separated, `E` a `Y`-perfect and `K` a pseudo-coherent object of
`D(𝒪_X)`.  Stacks 0DKY gives a pseudo-coherent `L ∈ D(𝒪_Y)` with
`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})` after every base change.  This file
assembles the proof of the source from the propositions of
`StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps`: the three inputs not yet proved
here (Stacks 0DKB, Stacks 0DKX, Stacks 0DKS (2)) and the four internal steps.  Nothing is
registered: the inputs are pending.

## Main results

* `AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible_of_steps`: the form of
  Stacks 0DKY that Stacks 0DLC consumes, with one `L` carrying both the objectwise base change
  isomorphisms and the natural isomorphism of relative Hom functors.
* `AlgebraicGeometry.Space.relativeDerivedHomDualExists_of_steps`,
  `AlgebraicGeometry.Space.relativeDerivedHomDualExistsNatural_of_steps`: the two other consumer
  forms.
* `AlgebraicGeometry.Space.exists_isPseudoCoherent_pushforward_sheafHom_iso_dual_of_steps`: the
  statement of Stacks 0DKY, and `relativeDerivedHomDualExists_of_stacks0DKY`, which reads it as
  the consumer proposition `AlgebraicGeometry.Space.RelativeDerivedHomDualExists`.

## Implementation notes

The steps of the source, with `Kₙ` indexed from `0` as in Stacks 0DKB:

1. `K = hocolim Kₙ` with `Kₙ` perfect and `Kₙ ⟶ K` an isomorphism on `τ_{≥ -(n+1)}`;
2. `Mₙ = Rf_* R𝓗om(Kₙ, E)` is perfect, and the base change map of Stacks 07A7 on
   `R𝓗om(Kₙ, E) = Kₙ^∨ ⊗^L E` is invertible (Stacks 08JJ, 0DKS, 0DKX);
3. `Lₙ = Mₙ^∨`, with `Lₙ^∨ ≅ Mₙ` by biduality
   (`AlgebraicGeometry.Space.smallEtaleDerivedBidualSystemIso`);
4. the window and the fibre test make `Lₙ ⟶ Lₙ₊₁` an isomorphism on cohomology in degrees
   `> -(a + n + 1)`, so the coprojections of `L = hocolim Lₙ` are isomorphisms in degrees
   `> -a - 1 - n` (Stacks 0CRK) and `L` is pseudo-coherent (Stacks 0CRJ and 0DKB);
5. both sides of the formula after base change are derived limits of `n ↦ Lg^*Mₙ`
   (Stacks 0A0A on `X'` and on `Y'`, Stacks 0A07, Stacks 08JF with 08JJ, Stacks 07A7);
6. the natural form is the naturality step.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A natural isomorphism carries the invertibility of the image of a morphism under a functor
from one functor to the other. -/
theorem isIso_map_map_of_iso {J C D : Type*} [Category J] [Category C] [Category D]
    {Φ Ψ : J ⥤ C} (e : Φ ≅ Ψ) (H : C ⥤ D) {a b : J} (h : a ⟶ b) (hΨ : IsIso (H.map (Ψ.map h))) :
    IsIso (H.map (Φ.map h)) := by
  rw [← NatIso.naturality_2 e h, H.map_comp, H.map_comp]
  infer_instance

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse system `n ↦ Rf_* R𝓗om(Kₙ, E)` on `Y` of a system `(Kₙ)` of `D(𝒪_X)`. -/
abbrev pushforwardHomSystem (F : ℕ ⥤ derivedModules B S hS X) (E : derivedModules B S hS X) :
    ℕᵒᵖ ⥤ derivedModules B S hS Y :=
  F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E ⋙ spaceDerivedPushforward B S hS f

/-- **The base change of the system `n ↦ Rf_* R𝓗om(Kₙ, E)`**: along a cartesian square
`X' = X ×_Y Y'`, for a system of perfect objects on whose internal Homs into `E` the base change
map of Stacks 07A7 is invertible, `Lg^* Rf_* R𝓗om(Kₙ, E) ≅ Rf'_* R𝓗om(L(g')^*Kₙ, L(g')^*E)`
as inverse systems (Stacks 07A7 and 08JF with 08JJ). -/
theorem nonempty_pushforwardHomSystem_comp_pull_iso (hH : PullSheafHomPerfectSystemIso B S hS)
    {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (hpb : IsPullback g' f' f g) (F : ℕ ⥤ derivedModules B S hS X)
    (hF : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n))
    (E : derivedModules B S hS X)
    (hbc : ∀ n, IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj n))).obj E))) :
    Nonempty (pushforwardHomSystem f F E ⋙ (smallEtaleDerivedPullbackData B S hS).pull g ≅
      pushforwardHomSystem f' (F ⋙ (smallEtaleDerivedPullbackData B S hS).pull g')
        (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) := by
  obtain ⟨φ⟩ := hH g' F hF E
  let bc : (F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E) ⋙
      smallEtaleDerivedModulePushforward B S hS f ⋙ smallEtaleDerivedModulePullback B S hS g ≅
      (F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E) ⋙
        smallEtaleDerivedModulePullback B S hS g' ⋙ smallEtaleDerivedModulePushforward B S hS f' :=
    NatIso.ofComponents
      (fun n => @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w
        (((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj n.unop))).obj E)) (hbc n.unop))
      (fun h => smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f g f' g' hpb.w _)
  exact ⟨Functor.isoWhiskerLeft (F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E)
      (Functor.isoWhiskerRight
        (eqToIso (derivedPushforward_eq_spaceDerivedPushforward B S hS f).symm)
        ((smallEtaleDerivedPullbackData B S hS).pull g)) ≪≫ bc ≪≫
    Functor.isoWhiskerRight φ (smallEtaleDerivedModulePushforward B S hS f') ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (derivedPushforward_eq_spaceDerivedPushforward B S hS f'))⟩

/-- `R𝓗om(P, E) = P^∨ ⊗^L E` is `Y`-perfect for `P` perfect and `E` `Y`-perfect (Stacks 08JJ
and Stacks 0DKS, assertion (2)). -/
theorem isPerfectRelativeToCanonical_smallEtaleDerivedSheafHom
    (h0DKS : TensorPerfectRelativelyPerfect B S hS) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) {P : derivedModules B S hS X}
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P) {E : derivedModules B S hS X}
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hlfp E) :
    IsPerfectRelativeToCanonical B S hS f hflat hlfp
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E) := by
  have : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasDerivedCategory (SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over U)) :=
    fun _ => HasDerivedCategory.standard _
  exact (isClosedUnderIsomorphisms_isPerfectRelativeToCanonical B S hS f hflat hlfp).of_iso
    (smallEtaleDerivedSheafHomIsoTensorDual B S hS X P E hP).symm
    (h0DKS f hflat hlfp _ E (isPerfect_smallEtaleDerivedDual B S hS X P hP) hE)

/-- **The transition maps of a perfect approximation are isomorphisms in high degrees**: if the
coprojections `cₙ : Kₙ ⟶ K` of `K = hocolim Kₙ` are isomorphisms on cohomology in degrees
`≥ -(n + 1)`, so are the transition maps `Kₙ ⟶ Kₙ₊₁`. -/
theorem isIso_homologyFunctor_map_transition_of_coprojections {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {F : ℕ ⥤ DerivedCategory C} [HasCoproduct F.obj]
    {K : DerivedCategory C} {c : ∀ n, F.obj n ⟶ K}
    (hc : ∀ (n : ℕ) (i : ℤ), -((n : ℤ) + 1) ≤ i →
      IsIso ((DerivedCategory.homologyFunctor C i).map (c n)))
    (hFK : IsHomotopyColimitWith F K c) (n : ℕ) (i : ℤ) (hi : -((n : ℤ) + 1) ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map (F.map (homOfLE (Nat.le_succ n)))) := by
  have h₁ := hc n i hi
  have := hc (n + 1) i (by push_cast; omega)
  rw [hFK.coprojection_eq n, Functor.map_comp] at h₁
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C i).map (c (n + 1)))

/-- **The fibre test of Stacks 0DKY on the system of duals** (step 4 of the source): if the
transition maps of `n ↦ Mₙ = Rf_* R𝓗om(Kₙ, E)` are isomorphisms on cohomology in degrees
`≤ a + n + 1` after every base change, then the transition maps of the system of duals
`n ↦ Mₙ^∨` are isomorphisms on cohomology in degrees `> -(a + n + 1)`. -/
theorem isIso_homologyFunctor_map_dual_pushforwardHomSystem
    (hH : PullSheafHomPerfectSystemIso B S hS) (hF : PerfectDualIsoOfFieldFibres B S hS)
    (F : ℕ ⥤ derivedModules B S hS X)
    (hFp : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n))
    (E : derivedModules B S hS X)
    (hM : ∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((pushforwardHomSystem f F E).obj (op n)))
    (hbc : ∀ (n : ℕ) {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
      (hpb : IsPullback g' f' f g),
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w
        (((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj n))).obj E)))
    (a : ℤ)
    (hwin : ∀ (n : ℕ) {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (g : Y' ⟶ Y), IsPullback g' f' f g → ∀ i : ℤ, i ≤ a + n + 1 →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
        ((spaceDerivedPushforward B S hS f').map
          (((smallEtaleDerivedSheafHom B S hS X').map
            (((smallEtaleDerivedPullbackData B S hS).pull g').map
              (F.map (homOfLE (Nat.le_succ n)))).op).app
                (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)))))
    (n : ℕ) (i : ℤ) (hi : -(a + n + 1) < i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
      (((pushforwardHomSystem f F E).rightOp ⋙
        (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y)).map
          (homOfLE (Nat.le_succ n)))) := by
  refine hF Y ((pushforwardHomSystem f F E).map (homOfLE (Nat.le_succ n)).op) (hM n) (hM (n + 1))
    (a + n + 1) (fun T₀ _ j hj => ?_) i (by omega)
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom
  obtain ⟨Φ⟩ := nonempty_pushforwardHomSystem_comp_pull_iso f hH _ _ _ hpb F hFp E
    (fun m => hbc m _ _ _ hpb)
  exact isIso_map_map_of_iso Φ _ (homOfLE (Nat.le_succ n)).op (hwin n _ _ _ hpb j hj)

/-- **The derived colimit `L` of the duals is pseudo-coherent** (Stacks 0DKB, `⇐`): if
`L = hocolim Lₙ` with `Lₙ` perfect and coprojections that are isomorphisms on cohomology in
degrees `> b - n`, then `L` is pseudo-coherent.  After discarding the first `b + 2` terms
(Stacks 0CRJ) the coprojections are isomorphisms on `τ_{≥ -(n + 1)}`, which is the shape of
Stacks 0DKB. -/
theorem isPseudoCoherent_of_isHomotopyColimitWith_of_isIso_homology
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    {Z : AlgebraicSpaces B S hS} (hqc : IsQuasiCompactSpace B S hS Z.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Z.1) {G : ℕ ⥤ derivedModules B S hS Z}
    [HasCoproduct G.obj] {L : derivedModules B S hS Z} {c' : ∀ n, G.obj n ⟶ L}
    (hGp : ∀ n, (smallEtaleRingedSite B S hS Z.1 Z.2).IsPerfect (G.obj n)) (b : ℤ)
    (hc' : ∀ (n : ℕ) (i : ℤ), b - (n : ℤ) < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) i).map (c' n)))
    (hL : IsHomotopyColimitWith G L c') :
    (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherent L := by
  have := hasColimitsOfShape_discrete_nat_derivedModules B S hS Z
  have hm : StrictMono (fun i : ℕ => i + (b + 2).toNat) := fun _ _ h => Nat.add_lt_add_right h _
  have hb : b + 2 ≤ ((b + 2).toNat : ℤ) := Int.self_le_toNat (b + 2)
  refine (h0DKB hZ Z hqc hqs L).2 ⟨hm.monotone.functor ⋙ G, fun i => c' (i + (b + 2).toNat),
    fun i => hGp _, fun i => ?_, hL.comp_strictMono hm⟩
  rw [Stacks.PseudoCoherentHocolim.isIso_truncGE_map_iff]
  intro j hj
  exact hc' _ j (by push_cast; omega)

/-- **The formula of Stacks 0DKY after a base change**: for `K = hocolim Kₙ` with `Kₙ` perfect,
an inverse system of duals `n ↦ Lₙ` with `Lₙ^∨ ≅ Rf_* R𝓗om(Kₙ, E)`, `L = hocolim Lₙ` and a
cartesian square on whose terms the base change map is invertible,
`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})`.  Both sides are derived limits of the
same inverse system (Stacks 0A0A on `X'` and on `Y'`, and `Rf'_*` preserves derived limits). -/
theorem nonempty_pushforward_sheafHom_pull_iso_dual (hH : PullSheafHomPerfectSystemIso B S hS)
    (F : ℕ ⥤ derivedModules B S hS X) [HasCoproduct F.obj]
    (hFp : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n))
    (E : derivedModules B S hS X) {K : derivedModules B S hS X} (hFK : IsHomotopyColimit F K)
    (G : ℕ ⥤ derivedModules B S hS Y) [HasCoproduct G.obj]
    (hGp : ∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect (G.obj n))
    {L : derivedModules B S hS Y} (hL : IsHomotopyColimit G L)
    (θ : G.op ⋙ (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y) ≅
      pushforwardHomSystem f F E)
    {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (hpb : IsPullback g' f' f g)
    (hbc : ∀ n, IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj n))).obj E))) :
    Nonempty ((spaceDerivedPushforward B S hS f').obj
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
            (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
      smallEtaleDerivedDual B S hS Y' (((smallEtaleDerivedPullbackData B S hS).pull g).obj L)) := by
  have hF' : HasCoproduct (F ⋙ (smallEtaleDerivedPullbackData B S hS).pull g').obj :=
    (hasColimitsOfShape_discrete_nat_derivedModules B S hS X').has_colimit _
  have hG' : HasCoproduct (G ⋙ (smallEtaleDerivedPullbackData B S hS).pull g).obj :=
    (hasColimitsOfShape_discrete_nat_derivedModules B S hS Y').has_colimit _
  have := hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS X'
  have := hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS Y'
  have : PreservesColimitsOfSize.{0, 0} ((smallEtaleDerivedPullbackData B S hS).pull g') :=
    (smallEtaleDerivedPullPushAdjunction B S hS g').leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} ((smallEtaleDerivedPullbackData B S hS).pull g) :=
    (smallEtaleDerivedPullPushAdjunction B S hS g).leftAdjoint_preservesColimits
  have : ((smallEtaleDerivedPullbackData B S hS).pull g').IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS g'
  have : ((smallEtaleDerivedPullbackData B S hS).pull g).IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS g
  have h₁ := @isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit_of_hasProduct B S hS X'
    (F ⋙ (smallEtaleDerivedPullbackData B S hS).pull g') hF'
    (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)
    ((hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS X').has_limit _) _
    (hFK.map ((smallEtaleDerivedPullbackData B S hS).pull g'))
  obtain ⟨hP, h₂⟩ := @isDerivedLimit_spaceDerivedPushforward B S hS X' Y' f' _
    ((hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS X').has_limit _) _ h₁
  have h₃ := @isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit_of_hasProduct B S hS Y'
    (G ⋙ (smallEtaleDerivedPullbackData B S hS).pull g) hG' (structureObject B S hS Y')
    ((hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS Y').has_limit _) _
    (hL.map ((smallEtaleDerivedPullbackData B S hS).pull g))
  obtain ⟨Φ⟩ := nonempty_pushforwardHomSystem_comp_pull_iso f hH g' f' g hpb F hFp E hbc
  obtain ⟨ψ⟩ := hH g G hGp (structureObject B S hS Y)
  exact @IsDerivedLimit.nonempty_iso _ _ _ _ _ _ _ _ hP _ _ h₂ (@IsDerivedLimit.of_natIso
    _ _ _ _ _ _ _ _ _ ((hasLimitsOfShape_discrete_nat_smallEtaleDerived B S hS Y').has_limit _) hP
    (Functor.isoWhiskerLeft (G ⋙ (smallEtaleDerivedPullbackData B S hS).pull g).op
      ((smallEtaleDerivedSheafHom B S hS Y').flip.mapIso
        (smallEtaleDerivedPullStructureIso B S hS g).symm) ≪≫ ψ.symm ≪≫
      Functor.isoWhiskerRight θ ((smallEtaleDerivedPullbackData B S hS).pull g) ≪≫ Φ) _ h₃)

variable (B S hS) in
/-- **Stacks 0DKY, assembled from its steps** (unregistered): the content of Stacks 0DKY in the
form the proof of Stacks 0DLC consumes,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`,
from the three inputs not yet proved here (Stacks 0DKB, Stacks 0DKX, Stacks 0DKS (2)) and the
four internal steps of the proof (the window, the fibre test, the naturality step and
Stacks 08JF with 08JJ along a system), all stated in
`StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps`.

The proof follows the source: write `K = hocolim Kₙ` with `Kₙ` perfect (Stacks 0DKB); the
`Mₙ = Rf_* R𝓗om(Kₙ, E)` are perfect and commute with base change (Stacks 0DKS, 0DKX); the
transition maps of `Lₙ = Mₙ^∨` are isomorphisms in high degrees (the window and the fibre
test), so `L = hocolim Lₙ` is pseudo-coherent (Stacks 0CRK, 0CRJ, 0DKB); both
`Rf'_* R𝓗om(L(g')^*K, L(g')^*E)` and `R𝓗om(Lg^*L, 𝒪_{Y'})` are derived limits of
`n ↦ Lg^*Mₙ` (Stacks 0A0A); and the natural form is the naturality step. -/
theorem relativeDerivedHomDualExistsNaturalCompatible_of_steps
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hE : RelativelyPerfectHomWindow B S hS) (hF : PerfectDualIsoOfFieldFibres B S hS)
    (hG : RelativeDerivedHomDualNaturality B S hS) (hH : PullSheafHomPerfectSystemIso B S hS) :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS := by
  intro hZ X Y f hqc hqs hp hflat hfp K E hErel hK
  have := hasColimitsOfShape_discrete_nat_derivedModules B S hS X
  have := hasColimitsOfShape_discrete_nat_derivedModules B S hS Y
  obtain ⟨F, c, hFp, hFtr, hFK⟩ := (h0DKB hZ X
    (isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hqc f.hom hp.2.1.2)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2 hqs
      (isQuasiSeparated_of_isSeparated B S hS hp.1)) K).1 hK
  have hFc : ∀ (n : ℕ) (i : ℤ), -((n : ℤ) + 1) ≤ i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map (c n)) :=
    fun n => (Stacks.PseudoCoherentHocolim.isIso_truncGE_map_iff (c n) _).1 (hFtr n)
  have hX := fun n => h0DKX f hp hflat hfp _
    (isPerfectRelativeToCanonical_smallEtaleDerivedSheafHom f h0DKS hflat hfp.1 (hFp n) hErel)
  obtain ⟨a, ha⟩ := hE hZ f hqc hqs hp hflat hfp E hErel
  have hwin : ∀ (n : ℕ) {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (g : Y' ⟶ Y), IsPullback g' f' f g → ∀ i : ℤ, i ≤ a + n + 1 →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
        ((spaceDerivedPushforward B S hS f').map
          (((smallEtaleDerivedSheafHom B S hS X').map
            (((smallEtaleDerivedPullbackData B S hS).pull g').map
              (F.map (homOfLE (Nat.le_succ n)))).op).app
                (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)))) :=
    fun n _ _ g' f' g hpb i hi => ha g' f' g hpb (F.map (homOfLE (Nat.le_succ n))) (hFp n)
      (hFp (n + 1)) (-((n : ℤ) + 1))
      (fun j hj => isIso_homologyFunctor_map_transition_of_coprojections hFc hFK n j hj) i
      (by omega)
  have : HasCoproduct ((pushforwardHomSystem f F E).rightOp ⋙
      (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y)).obj :=
    (hasColimitsOfShape_discrete_nat_derivedModules B S hS Y).has_colimit _
  obtain ⟨L, c', hL⟩ := exists_isHomotopyColimitWith_of_hasCoproduct
    ((pushforwardHomSystem f F E).rightOp ⋙
      (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y))
  have hGp : ∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      (((pushforwardHomSystem f F E).rightOp ⋙
        (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y)).obj n) :=
    fun n => isPerfect_smallEtaleDerivedDual B S hS Y _ (hX n).1
  have hc' : ∀ (n : ℕ) (i : ℤ), (-a - 1) - (n : ℤ) < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map (c' n)) :=
    fun n i hi => @isIso_homologyFunctor_map_coprojection_smallEtale B S hS Y _
      ((hasColimitsOfShape_discrete_nat_derivedModules B S hS Y).has_colimit _) _ _ hL i n
      (fun k hk => isIso_homologyFunctor_map_dual_pushforwardHomSystem f hH hF F hFp E
        (fun m => (hX m).1) (fun m _ _ g' f' g hpb => (hX m).2 g' f' g hpb) a hwin k i
        (by omega))
  let θ := smallEtaleDerivedBidualSystemIso B S hS Y (pushforwardHomSystem f F E)
    (fun n => (hX n.unop).1)
  refine ⟨L, isPseudoCoherent_of_isHomotopyColimitWith_of_isIso_homology h0DKB hZ hqc hqs hGp
      (-a - 1) hc' hL, fun g' f' g hpb => ?_, hG hZ f hqc hqs hp hflat hfp K E hErel hK F c hFp
      hFc hFK _ L c' hGp ⟨-a - 1, hc'⟩ hL θ (fun n _ _ g' f' g hpb => (hX n).2 g' f' g hpb)
      ⟨a, fun n _ _ g' f' g hpb i hi => hwin n g' f' g hpb i (by omega)⟩⟩
  exact nonempty_pushforward_sheafHom_pull_iso_dual f hH F hFp E hFK.isHomotopyColimit _ hGp
    hL.isHomotopyColimit θ g' f' g hpb (fun n => (hX n).2 g' f' g hpb)

variable (B S hS) in
/-- **Stacks 0DKY, assembled from its remaining steps**: the window
(`AlgebraicGeometry.Space.relativelyPerfectHomWindow`) is proved, and the fibre test
`AlgebraicGeometry.Space.PerfectDualIsoOfFieldFibres` follows from Stacks 08JF with 08JJ along a
system (`AlgebraicGeometry.Space.perfectDualIsoOfFieldFibres_of_pullSheafHomPerfectSystemIso`);
what is left are the three held inputs, the naturality step and Stacks 08JF with 08JJ along a
system. -/
theorem relativeDerivedHomDualExistsNaturalCompatible_of_steps'
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hG : RelativeDerivedHomDualNaturality B S hS) (hH : PullSheafHomPerfectSystemIso B S hS) :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS :=
  relativeDerivedHomDualExistsNaturalCompatible_of_steps B S hS h0DKB h0DKX h0DKS
    (relativelyPerfectHomWindow B S hS)
    (perfectDualIsoOfFieldFibres_of_pullSheafHomPerfectSystemIso B S hS hH) hG hH

variable (B S hS) in
/-- The objectwise form of Stacks 0DKY, `AlgebraicGeometry.Space.RelativeDerivedHomDualExists`,
from the steps. -/
theorem relativeDerivedHomDualExists_of_steps
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hE : RelativelyPerfectHomWindow B S hS) (hF : PerfectDualIsoOfFieldFibres B S hS)
    (hG : RelativeDerivedHomDualNaturality B S hS) (hH : PullSheafHomPerfectSystemIso B S hS) :
    RelativeDerivedHomDualExists B S hS :=
  (relativeDerivedHomDualExistsNaturalCompatible_of_steps B S hS h0DKB h0DKX h0DKS hE hF hG
    hH).relativeDerivedHomDualExists

variable (B S hS) in
/-- The natural form of Stacks 0DKY, `AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNatural`,
from the steps. -/
theorem relativeDerivedHomDualExistsNatural_of_steps
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hE : RelativelyPerfectHomWindow B S hS) (hF : PerfectDualIsoOfFieldFibres B S hS)
    (hG : RelativeDerivedHomDualNaturality B S hS) (hH : PullSheafHomPerfectSystemIso B S hS) :
    RelativeDerivedHomDualExistsNatural B S hS :=
  (relativeDerivedHomDualExistsNaturalCompatible_of_steps B S hS h0DKB h0DKX h0DKS hE hF hG
    hH).relativeDerivedHomDualExistsNatural

/-! ### The statement of Stacks 0DKY -/

/-- **Stacks 0DKY** (unregistered: it rests on Stacks 0DKB, not yet proved here, Stacks 0DKX, not
yet proved here, and Stacks 0DKS (2), not yet proved here, all pending, and on the internal steps
of `StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps`).  Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` with `Y` quasi-compact and quasi-separated and `f` proper,
flat and of finite presentation, let `E` be `Y`-perfect and `K` pseudo-coherent in `D(𝒪_X)`.
Then there is a pseudo-coherent `L` in `D(𝒪_Y)` with
`Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`, and the same is true after arbitrary base change: for every
cartesian square `X' = X ×_Y Y'` with projections `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})`. -/
theorem exists_isPseudoCoherent_pushforward_sheafHom_iso_dual_of_steps
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hE : RelativelyPerfectHomWindow B S hS) (hF : PerfectDualIsoOfFieldFibres B S hS)
    (hG : RelativeDerivedHomDualNaturality B S hS) (hH : PullSheafHomPerfectSystemIso B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hp : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (K E : derivedModules B S hS X) (hE' : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K) :
    ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
      Nonempty ((spaceDerivedPushforward B S hS f).obj
          (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) ≅
        smallEtaleDerivedDual B S hS Y L) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
        IsPullback g' f' f g →
        Nonempty ((spaceDerivedPushforward B S hS f').obj
            (((smallEtaleDerivedSheafHom B S hS X').obj
              (op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
                (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
          smallEtaleDerivedDual B S hS Y'
            (((smallEtaleDerivedPullbackData B S hS).pull g).obj L)) :=
  relativeDerivedHomDualExists_of_steps B S hS h0DKB h0DKX h0DKS hE hF hG hH hZ f hqc hqs hp
    hflat hfp K E hE' hK

variable (B S hS) in
/-- The statement of Stacks 0DKY, `exists_isPseudoCoherent_pushforward_sheafHom_iso_dual_of_steps`,
read as a proposition over all its data, is the consumer proposition
`AlgebraicGeometry.Space.RelativeDerivedHomDualExists`. -/
theorem relativeDerivedHomDualExists_of_stacks0DKY
    (h : ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
      IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
      IsProper B S hS f.hom →
      ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
        (K E : derivedModules B S hS X),
        IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
        ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
          Nonempty ((spaceDerivedPushforward B S hS f).obj
              (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) ≅
            smallEtaleDerivedDual B S hS Y L) ∧
          ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
            IsPullback g' f' f g →
            Nonempty ((spaceDerivedPushforward B S hS f').obj
                (((smallEtaleDerivedSheafHom B S hS X').obj
                  (op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
                    (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
              smallEtaleDerivedDual B S hS Y'
                (((smallEtaleDerivedPullbackData B S hS).pull g).obj L))) :
    RelativeDerivedHomDualExists B S hS :=
  fun hZ _ _ f hqc hqs hp hflat hfp K E hE hK => h hZ f hqc hqs hp hflat hfp K E hE hK

end AlgebraicGeometry.Space

end
