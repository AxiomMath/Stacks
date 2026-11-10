module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDualVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral

/-!
# The fibre test of the proof of Stacks 0DKY

Let `ψ : M' ⟶ M` be a morphism of perfect objects of `D(𝒪_Y)`, for `Y` an algebraic space, such
that at every point `y : Spec(k) ⟶ Y` with values in a field the derived pullback `Ly^*ψ` is an
isomorphism on cohomology in degrees `≤ j`.  Then the dual map `ψ^∨ : M^∨ ⟶ M'^∨` is an
isomorphism on cohomology in degrees `> -j`.  This is step 4 of the proof of Stacks 0DKY,
`AlgebraicGeometry.Space.PerfectDualIsoOfFieldFibres`, which the source reads off Stacks 0BCD.

## Main results

* `AlgebraicGeometry.Space.perfectDualIsoOfFieldFibres_of_pullSheafHomPerfectSystemIso`: the
  proposition `AlgebraicGeometry.Space.PerfectDualIsoOfFieldFibres`, granted
  `AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` (Stacks 08JF with 08JJ; internal to the
  proof of Stacks 0DKY, pending).
* `AlgebraicGeometry.Space.exists_distinguished_smallEtaleDerivedDual`: the derived dual on an
  algebraic space carries a distinguished triangle to a distinguished triangle (Stacks 08JC).
* `AlgebraicGeometry.Space.subsingleton_smallEtaleDerivedDual_hom_shift_of_isGE`: for a perfect
  `N` with no cohomology below degree `j`, `Hom(N^∨, 𝒪[m]) = 0` for `m < j`.

## The argument

Let `C` be the cone of `ψ`; it is perfect (Stacks 08G9).  At a field point `y`, the long exact
cohomology sequence of `Ly^*M' ⟶ Ly^*M ⟶ Ly^*C` shows that `Ly^*C` has no cohomology below
degree `j`.  The dual commutes with derived pullback for perfect objects (Stacks 08JF, the
hypothesis), so `Hom(Ly^*(C^∨), 𝒪[m]) = Hom((Ly^*C)^∨, 𝒪[m]) = H^m(Spec k, (Ly^*C)^∨∨)
= H^m(Spec k, Ly^*C)`, which vanishes for `m < j` (Stacks 08JA and 08JJ).  By the fibre-to-stalk
step on `Y` (`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`, Nakayama's lemma at the top
degree on affine étale charts), applied to `C^∨[-j]`, the dual `C^∨` has no cohomology above
degree `-j`.  This replaces the source's appeal to Stacks 0BCD (a Tor amplitude `[j, m]` for `C`
near every point), of which only this consequence is used.  Finally `C^∨ ⟶ M^∨ ⟶ M'^∨` is a
distinguished triangle, and its long exact cohomology sequence gives the claim.

Nothing is registered: the hypothesis is internal to the proof of Stacks 0DKY and pending.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08G9](https://stacks.math.columbia.edu/tag/08G9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

/-! ### A consequence of the long exact cohomology sequence -/

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The second map of a distinguished triangle whose first object lives in degrees `≤ t` is an
isomorphism on cohomology in degrees `> t`.** -/
theorem isIso_homologyMap_mor₂_of_isLE_obj₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (t : ℤ) (hT₁ : T.obj₁.IsLE t) (i : ℤ) (hi : t < i) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have hm : Mono ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT i).2
      ((isZero_of_isLE T.obj₁ t i hi).eq_of_src _ _)
  have he : Epi ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)).2
      ((isZero_of_isLE T.obj₁ t (i + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end DerivedCategory

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

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The derived category of `𝒪_X`-modules at the spelling `SheafOfModules (𝒪 of the small étale
ringed topos)` in which `AlgebraicGeometry.Space.smallEtaleDerivedDual` and the derived
equivalence with the model are stated, at the standard model that
`AlgebraicGeometry.Space.derivedModules` is formed at. -/
local instance instRingedToposModulesHasDerivedCategory (X : AlgebraicSpaces B S hS) :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  HasDerivedCategory.standard _

/-- The derived category of the equi-universe model of the small étale ringed site, at the
standard model at which `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` reads the derived
internal Hom of the model. -/
local instance instSmallEtaleModelModulesHasDerivedCategory (X : AlgebraicSpaces B S hS) :
    HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X.1 X.2).O)) :=
  HasDerivedCategory.standard _

/-! ### The derived dual on an algebraic space -/

/-- **Stacks 08JC for the derived dual on an algebraic space.**  For a distinguished triangle
`T` of `D(𝒪_X)`, the maps `(T.obj₃)^∨ ⟶ (T.obj₂)^∨ ⟶ (T.obj₁)^∨` induced by `T.mor₂` and
`T.mor₁` extend to a distinguished triangle.  On the equi-universe model this is
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, and the derived equivalence
with the model is triangulated in both directions. -/
theorem exists_distinguished_smallEtaleDerivedDual (X : AlgebraicSpaces B S hS)
    (T : Triangle (derivedModules B S hS X)) (hT : T ∈ distTriang _) :
    ∃ δ : smallEtaleDerivedDual B S hS X T.obj₁ ⟶
        (smallEtaleDerivedDual B S hS X T.obj₃)⟦(1 : ℤ)⟧,
      Triangle.mk (((smallEtaleDerivedSheafHom B S hS X).map T.mor₂.op).app
          (structureObject B S hS X))
        (((smallEtaleDerivedSheafHom B S hS X).map T.mor₁.op).app (structureObject B S hS X))
        δ ∈ distTriang _ := by
  let E := modulesEquivModelModules B S hS X.1 X.2
  have : E.functor.Additive := smallEtaleModelModulesEquivalence_functor_additive B S hS X
  obtain ⟨δ', hδ'⟩ := RingedSite.exists_distinguished_derivedSheafHom
    (smallEtaleModelRingedSite B S hS X.1 X.2)
    (E.functor.mapDerivedCategory.obj (structureObject B S hS X))
    (E.functor.mapDerivedCategory.mapTriangle.obj T)
    (E.functor.mapDerivedCategory.map_distinguished T hT)
  exact ⟨_, E.inverse.mapDerivedCategory.map_distinguished _ hδ'⟩

/-- **Negative extensions out of the dual of a perfect object.**  If `N` in `D(𝒪_X)` is perfect
with no cohomology below degree `j`, then `Hom(N^∨, 𝒪_X[m]) = 0` for `m < j`: it is
`H^m(X, N^∨∨) = H^m(X, N) = Hom(𝒪_X, N[m])` (Stacks 08JA and 08JJ), and `N[m]` has no cohomology
in degrees `≤ 0`. -/
theorem subsingleton_smallEtaleDerivedDual_hom_shift_of_isGE (X : AlgebraicSpaces B S hS)
    (N : derivedModules B S hS X) (hN : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect N)
    (j : ℤ) (hNj : N.IsGE j) (m : ℤ) (hm : m < j) :
    Subsingleton (smallEtaleDerivedDual B S hS X N ⟶ (structureObject B S hS X)⟦m⟧) := by
  refine (homShiftEquivStructureHomSheafHom B S hS _ (structureObject B S hS X) m
    ).subsingleton_congr.2 ?_
  refine ((Iso.refl _).homCongr
    ((shiftFunctor _ m).mapIso (smallEtaleDerivedBidualIso B S hS X N hN))).subsingleton_congr.2 ?_
  change Subsingleton (structureObject B S hS X ⟶ N⟦m⟧)
  have : (N⟦m⟧).IsGE (j - m) := DerivedCategory.TStructure.t.isGE_shift N j m (j - m)
  have : (N⟦m⟧).IsGE 1 := DerivedCategory.TStructure.t.isGE_of_ge _ 1 (j - m) (by omega)
  exact ⟨fun a b => (DerivedCategory.TStructure.t.zero a 0 1).trans
    (DerivedCategory.TStructure.t.zero b 0 1).symm⟩

/-- **The derived pullback of the dual of a perfect object is the dual of its derived pullback**,
granted `AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` (Stacks 08JF and 08JJ; internal,
pending), read at a constant system and at `E = 𝒪_Y`, with `Lg^*𝒪_Y = 𝒪_X`. -/
theorem nonempty_pull_smallEtaleDerivedDual_iso (hH : PullSheafHomPerfectSystemIso B S hS)
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (C : derivedModules B S hS Y)
    (hC : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect C) :
    Nonempty (((smallEtaleDerivedPullbackData B S hS).pull g).obj
        (smallEtaleDerivedDual B S hS Y C) ≅
      smallEtaleDerivedDual B S hS X (((smallEtaleDerivedPullbackData B S hS).pull g).obj C)) := by
  obtain ⟨e⟩ := hH g ((Functor.const ℕ).obj C) (fun _ => hC) (structureObject B S hS Y)
  exact ⟨e.app (Opposite.op 0) ≪≫
    ((smallEtaleDerivedSheafHom B S hS X).obj
      (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull g).obj C))).mapIso
      (smallEtaleDerivedPullStructureIso B S hS g)⟩

/-- Morphisms out of a shift: `Hom(Z[-j], G[i]) ≃ Hom(Z, G[i + j])`. -/
def homShiftNegEquiv {D : Type*} [Category D] [HasShift D ℤ] (Z G : D) (i j : ℤ) :
    (Z⟦-j⟧ ⟶ G⟦i⟧) ≃ (Z ⟶ G⟦i + j⟧) :=
  ((shiftEquiv D j).fullyFaithfulFunctor.homEquiv).trans
    (((shiftFunctorCompIsoId D (-j) j (by omega)).app Z).homCongr
      ((shiftFunctorAdd' D i j (i + j) rfl).app G).symm)

/-! ### The fibre test -/

/-- **The dual of a perfect object with connective field fibres is coconnective.**  Granted
`AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` (internal to the proof of Stacks 0DKY,
pending): if `C` in `D(𝒪_Y)` is perfect and at every point `y : Spec(k) ⟶ Y` with values in a
field `Ly^*C` has no cohomology below degree `j`, then `C^∨` has no cohomology above degree `-j`.

At a field point, `Hom(Ly^*(C^∨[-j]), 𝒪[i]) = Hom((Ly^*C)^∨, 𝒪[i + j])` vanishes for `i < 0`
(`AlgebraicGeometry.Space.subsingleton_smallEtaleDerivedDual_hom_shift_of_isGE`), so
`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE` applies to the perfect, hence
pseudo-coherent, object `C^∨[-j]`. -/
theorem isLE_smallEtaleDerivedDual_of_forall_isFieldObject
    (hH : PullSheafHomPerfectSystemIso B S hS) (Y : AlgebraicSpaces B S hS)
    (C : derivedModules B S hS Y) (hC : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect C)
    (j : ℤ)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj C).IsGE j) :
    (smallEtaleDerivedDual B S hS Y C).IsLE (-j) := by
  let L : derivedModules B S hS Y := (smallEtaleDerivedDual B S hS Y C)⟦-j⟧
  have hLpc : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L :=
    RingedSite.isPseudoCoherent_of_isPerfect_general _
      (RingedSite.isPerfect_shift_general _
        (isPerfect_smallEtaleDerivedDual B S hS Y C hC) (-j))
  have : L.IsLE 0 := fieldFibreDualVanishingIsLE B S hS Y L hLpc fun T₀ hT₀ i hi => by
    obtain ⟨e⟩ := nonempty_pull_smallEtaleDerivedDual_iso B S hS hH T₀.hom C hC
    refine (((((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).commShiftIso (-j)).app
      (smallEtaleDerivedDual B S hS Y C) ≪≫
        (shiftFunctor (derivedModules B S hS _) (-j)).mapIso e).homCongr
          (Iso.refl _)).subsingleton_congr.2 ?_
    refine (homShiftNegEquiv _ _ i j).subsingleton_congr.2 ?_
    exact subsingleton_smallEtaleDerivedDual_hom_shift_of_isGE B S hS _ _
      (isPerfect_smallEtaleDerivedModulePullback T₀.hom C hC) j (hfib T₀ hT₀) (i + j)
      (by omega)
  have : (L⟦j⟧).IsLE (-j) := DerivedCategory.TStructure.t.isLE_shift L 0 j (-j)
  let e : L⟦j⟧ ≅ smallEtaleDerivedDual B S hS Y C :=
    (shiftFunctorCompIsoId (derivedModules B S hS Y) (-j) j (by omega)).app _
  exact DerivedCategory.TStructure.t.isLE_of_iso e (-j)

/-- **The fibre test of the proof of Stacks 0DKY** (step 4; internal), granted
`AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` (Stacks 08JF with 08JJ, internal to the
proof of Stacks 0DKY, pending): the proposition
`AlgebraicGeometry.Space.PerfectDualIsoOfFieldFibres`, exactly as stated there.  For a morphism
`ψ : M' ⟶ M` of perfect objects of `D(𝒪_Y)` whose derived pullback to every point with values
in a field is an isomorphism on cohomology in degrees `≤ j`, the dual `ψ^∨` is an isomorphism on
cohomology in degrees `> -j`.

The cone `C` of `ψ` is perfect (Stacks 08G9,
`AlgebraicGeometry.RingedSite.isPerfect_obj₃_of_distinguished_general`), its field fibres have
no cohomology below degree `j`, so `C^∨` has none above degree `-j`
(`AlgebraicGeometry.Space.isLE_smallEtaleDerivedDual_of_forall_isFieldObject`), and
`C^∨ ⟶ M^∨ ⟶ M'^∨` is distinguished
(`AlgebraicGeometry.Space.exists_distinguished_smallEtaleDerivedDual`). -/
theorem perfectDualIsoOfFieldFibres_of_pullSheafHomPerfectSystemIso
    (hH : PullSheafHomPerfectSystemIso B S hS) : PerfectDualIsoOfFieldFibres B S hS := by
  intro Y M M' ψ hM hM' j hfib i hi
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle ψ
  have hC : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect C :=
    RingedSite.isPerfect_obj₃_of_distinguished_general _ _ hT hM' hM
  have hCfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj C).IsGE j := fun T₀ hT₀ => by
    have : ((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).IsTriangulated :=
      isTriangulated_smallEtaleDerivedModulePullback B S hS T₀.hom
    -- the cone of a map which is an isomorphism on cohomology in degrees `≤ j` lives in degrees
    -- `≥ j` (as `Stacks.Cohomology.BoxKunneth.isGE_obj₃_of_isIso_homologyMap_mor₁`)
    have hT' := ((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).map_distinguished _ hT
    rw [DerivedCategory.isGE_iff]
    intro i hi
    have h₁ := (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT' i).1
      (@IsIso.epi_of_iso _ _ _ _ _ (hfib T₀ hT₀ i (by omega)))
    have h₂ := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT' i (i + 1)).1
      (@IsIso.mono_of_iso _ _ _ _ _ (hfib T₀ hT₀ (i + 1) (by omega)))
    exact (DerivedCategory.HomologySequence.exact₃ _ hT' i (i + 1)).isZero_of_both_zeros h₁ h₂
  obtain ⟨δ, hδ⟩ := exists_distinguished_smallEtaleDerivedDual B S hS Y _ hT
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE_obj₁ _ hδ (-j)
    (isLE_smallEtaleDerivedDual_of_forall_isFieldObject B S hS hH Y C hC j hCfib) i hi

end AlgebraicGeometry.Space

end
