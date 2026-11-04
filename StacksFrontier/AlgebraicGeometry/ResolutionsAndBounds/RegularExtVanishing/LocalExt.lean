module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelComorphism
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension

/-!
# Vanishing of `Ext` near a point of a regular scheme, above the dimension of the local ring

Let `X` be a regular scheme, `F` a coherent `𝒪_X`-module and `x ∈ X` a point whose local ring has
dimension `c`. Then there is an open neighbourhood `V` of `x` such that
`Ext^k_W(F|_W, G|_W) = 0` for every affine open `W ⊆ V`, every quasi-coherent `G` and every
`k > c`.

This is the local input of the proof of [Stacks, Tag 0FZ3] (1): the local ring `𝒪_{X,x}` is
regular of dimension `c`, so it has global dimension `c` ([Stacks, Tag 00O7]) and the stalk `F_x`
has projective dimension at most `c`. That bound spreads to a neighbourhood by dimension shifting.
Over an affine neighbourhood `F` is a quotient of a finite free module `E`. If `F_x` is
projective, then it is free, `F` is free near `x`, and `Ext^k` out of a free module vanishes on
affines for `k ≥ 1` by Serre vanishing. Otherwise the kernel `K` of `E ⟶ F` has a stalk of
projective dimension one less, and `Ext^k(F, G)` sits between `Ext^k(E, G) = 0` and
`Ext^{k-1}(K, G)`.

## Main definitions

* `Stacks.RegularExtVanishing.ExtVanishesNear`: the vanishing of `Ext^k(F|_Y, G|_Y)` for
  `k ≥ m`, quasi-coherent `G` and affine `Y` mapping by an open immersion into a fixed
  neighbourhood of `x`.

## Main results

* `Stacks.RegularExtVanishing.extVanishesNear_of_hasProjectiveDimensionLT`: on an affine locally
  Noetherian scheme, a coherent module whose stalk at `x` has projective dimension `< m` has
  `Ext` vanishing near `x` in degrees `≥ m`.
* `Stacks.RegularExtVanishing.exists_nbhd_subsingleton_zExt`: the statement above, on a regular
  scheme, with `c ≥ dim 𝒪_{X,x}`.

## Implementation notes

`Ext` is `Abelian.zExt`, the group of morphisms `F[0] ⟶ G[0][k]` in the derived category at
`HasDerivedCategory.standard`. The neighbourhood condition quantifies over open immersions from
affine schemes rather than over affine opens. Moving between an open subscheme and the whole
scheme is then composition of open immersions, and no isomorphism of open subschemes needs
transporting.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 00O7](https://stacks.math.columbia.edu/tag/00O7)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.RegularExtVanishing

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Morphisms in the derived category out of objects placed in degree zero -/

section Derived

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **Dimension shifting.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, a morphism
`X₃[0] ⟶ B[k]` vanishes as soon as every morphism `X₂[0] ⟶ B[k]` and every morphism
`X₁[0] ⟶ B[k - 1]` does. -/
theorem subsingleton_hom_X₃_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (B : DerivedCategory C) (k : ℤ)
    (h₂ : Subsingleton ((DerivedCategory.singleFunctor C 0).obj S.X₂ ⟶ B⟦k⟧))
    (h₁ : Subsingleton ((DerivedCategory.singleFunctor C 0).obj S.X₁ ⟶ B⟦k - 1⟧)) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj S.X₃ ⟶ B⟦k⟧) := by
  have hT := hS.singleTriangle_distinguished
  have h₁' : Subsingleton
      (((DerivedCategory.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ ⟶ B⟦k⟧) := by
    let e : (B⟦k - 1⟧)⟦(1 : ℤ)⟧ ≅ B⟦k⟧ :=
      (shiftFunctorAdd' (DerivedCategory C) (k - 1) 1 k (by omega)).symm.app B
    refine (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _) e)).mp ?_
    exact (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_surjective.subsingleton
  refine subsingleton_of_forall_eq 0 fun w => ?_
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT w (h₂.elim _ _)
  rw [hg, h₁'.elim g 0, comp_zero]

/-- `Ext` is invariant under isomorphisms of both arguments. -/
theorem subsingleton_zExt_of_iso {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B') (k : ℤ)
    (h : Subsingleton (Abelian.zExt A' B' k)) : Subsingleton (Abelian.zExt A B k) :=
  (Equiv.subsingleton_congr (Iso.homCongr ((DerivedCategory.singleFunctor C 0).mapIso eA)
    ((shiftFunctor _ k).mapIso ((DerivedCategory.singleFunctor C 0).mapIso eB)))).mpr h

/-- `Ext` out of a zero object vanishes. -/
theorem subsingleton_zExt_of_isZero {A : C} (hA : IsZero A) (B : C) (k : ℤ) :
    Subsingleton (Abelian.zExt A B k) :=
  ⟨fun f g => ((DerivedCategory.singleFunctor C 0).map_isZero hA).eq_of_src f g⟩

/-- `Ext` out of a finite coproduct vanishes when it vanishes out of every summand. -/
theorem subsingleton_zExt_sigma {I : Type*} [Finite I] (A : I → C) (B : C) (k : ℤ)
    (h : ∀ i, Subsingleton (Abelian.zExt (A i) B k)) :
    Subsingleton (Abelian.zExt (∐ A) B k) := by
  have hc := isColimitOfPreserves (DerivedCategory.singleFunctor C 0) (coproductIsCoproduct A)
  exact ⟨fun f g => hc.hom_ext fun ⟨i⟩ => (h i).elim _ _⟩

end Derived

/-! ### `Ext` out of free modules on an affine scheme -/

section Free

/-- **`Ext` out of the structure sheaf of an affine scheme vanishes in positive degrees** into a
quasi-coherent module: it is the cohomology of that module ([Stacks, Tag 01XB]). -/
theorem subsingleton_zExt_unit {Y : Scheme.{u}} [IsAffine Y] (G : Y.Modules) [G.IsQuasicoherent]
    (k : ℤ) (hk : 1 ≤ k) :
    Subsingleton (Abelian.zExt (_root_.SheafOfModules.unit Y.ringCatSheaf) G k) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k by omega)
  have hz := Stacks.Cohomology.CechAffineCover.isZero_rightDerived_evaluation_of_isAffineOpen Y G ⊤
    (isAffineOpen_top Y) n (by omega)
  exact (derivedHomStructureSheafEquivCohomology Y G n).toEquiv.subsingleton_congr.mpr
    (ModuleCat.subsingleton_of_isZero hz)

/-- **`Ext` out of a finite free module on an affine scheme vanishes in positive degrees** into
a quasi-coherent module. -/
theorem subsingleton_zExt_free {Y : Scheme.{u}} [IsAffine Y] (I : Type u) [Finite I]
    (G : Y.Modules) [G.IsQuasicoherent] (k : ℤ) (hk : 1 ≤ k) :
    Subsingleton (Abelian.zExt (_root_.SheafOfModules.free (R := Y.ringCatSheaf) I) G k) :=
  subsingleton_zExt_sigma (fun _ : I => _root_.SheafOfModules.unit Y.ringCatSheaf) G k
    fun _ => subsingleton_zExt_unit G k hk

/-- The restriction of a free module along an open immersion is free on the same index set. -/
def restrictFreeIso {X Y : Scheme.{u}} (ι : Y ⟶ X) [IsOpenImmersion ι] (I : Type u) :
    Scheme.Modules.restrict (_root_.SheafOfModules.free (R := X.ringCatSheaf) I) ι ≅
      _root_.SheafOfModules.free (R := Y.ringCatSheaf) I :=
  PreservesCoproduct.iso (Scheme.Modules.restrictFunctor ι)
      (fun _ : I => _root_.SheafOfModules.unit X.ringCatSheaf) ≪≫
    Sigma.mapIso fun _ => Scheme.Modules.restrictUnitIso ι

end Free

/-! ### Open immersions into an open subscheme -/

section Lift

variable {X Y : Scheme.{u}} (V : X.Opens) (ι : Y ⟶ X) [IsOpenImmersion ι]
  (h : Set.range ι.base ⊆ V)

/-- An open immersion landing in `V` factors through the open subscheme `V`. -/
def liftToOpens : Y ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ι (by rwa [Scheme.Opens.range_ι])

omit [IsOpenImmersion ι] in
/-- The factorisation of `ι` through `V`, followed by the inclusion of `V`, is `ι`. -/
lemma liftToOpens_ι : liftToOpens V ι h ≫ V.ι = ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorisation of an open immersion through `V` is an open immersion. -/
instance : IsOpenImmersion (liftToOpens V ι h) := by
  have : IsOpenImmersion (liftToOpens V ι h ≫ V.ι) := by
    rw [liftToOpens_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ V.ι

/-- Restricting along `ι` is restricting to `V` and then along the factorisation. -/
def restrictLiftIso (M : X.Modules) :
    M.restrict ι ≅ (M.restrict V.ι).restrict (liftToOpens V ι h) :=
  ((Scheme.Modules.restrictFunctorCongr (liftToOpens_ι V ι h)).symm ≪≫
    Scheme.Modules.restrictFunctorComp (liftToOpens V ι h) V.ι).app M

end Lift

/-! ### Spreading a bound on the projective dimension of a stalk -/

/-- `Ext^k(F|_Y, G|_Y)` vanishes for `k ≥ m`, every quasi-coherent `G` and every affine `Y`
mapping by an open immersion into some fixed open neighbourhood of `x`. -/
def ExtVanishesNear {X : Scheme.{u}} (F : X.Modules) (x : X) (m : ℕ) : Prop :=
  ∃ V : X.Opens, x ∈ V ∧ ∀ (Y : Scheme.{u}) (ι : Y ⟶ X) [IsOpenImmersion ι] [IsAffine Y],
    Set.range ι.base ⊆ V → ∀ (G : X.Modules), G.IsQuasicoherent → ∀ k : ℤ, (m : ℤ) ≤ k →
      Subsingleton (Abelian.zExt (F.restrict ι) (G.restrict ι) k)

/-- The stalk of a free module of finite rank is projective over the local ring. -/
theorem projective_stalk_free {X : Scheme.{u}} (x : X) (I : Type u) [Finite I] :
    Projective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I)) := by
  have hunit : Projective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
      (_root_.SheafOfModules.unit X.ringCatSheaf)) := by
    have : Projective (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :=
      ModuleCat.projective_of_categoryTheory_projective _
    exact Projective.of_iso (Stacks.Duality.unitStalkModuleEquiv X x).toModuleIso.symm this
  have : ∀ _ : I, Projective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
      (_root_.SheafOfModules.unit X.ringCatSheaf)) := fun _ => hunit
  exact Projective.of_iso (PreservesCoproduct.iso (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
    (fun _ : I => _root_.SheafOfModules.unit X.ringCatSheaf)).symm inferInstance

/-- **Spreading a bound on the projective dimension of a stalk.** On an affine locally
Noetherian scheme, if the stalk at `x` of a coherent module `F` has projective dimension `< m`
over `𝒪_{X,x}`, then `Ext^k(F|_Y, G|_Y) = 0` for `k ≥ m` near `x`. -/
theorem extVanishesNear_of_hasProjectiveDimensionLT {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] :
    ∀ (m : ℕ) (F : X.Modules), _root_.SheafOfModules.IsCoherent F → ∀ x : X,
      HasProjectiveDimensionLT ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) m →
        ExtVanishesNear F x m
  | 0, F, hF, x, h => by
    have hz : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
      isZero_of_hasProjectiveDimensionLT_zero _
    have hz' : IsZero (F.presheaf.stalk x) :=
      have : Subsingleton (F.presheaf.stalk x) := ModuleCat.subsingleton_of_isZero hz
      AddCommGrpCat.isZero_of_subsingleton _
    obtain ⟨V, hxV, hV⟩ :=
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isOpen_isZero_restrict_of_isZero_stalk
        F hF.isFiniteType x hz'
    refine ⟨V, hxV, fun Y ι _ _ hι G _ k _ => ?_⟩
    exact subsingleton_zExt_of_isZero
      (((Scheme.Modules.restrictFunctor (liftToOpens V ι hι)).map_isZero hV).of_iso
        (restrictLiftIso V ι hι F)) _ _
  | 1, F, hF, x, h => by
    have : _root_.SheafOfModules.IsFiniteType F := hF.isFiniteType
    have hproj : Projective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr h
    have : Module.Projective (X.presheaf.stalk x)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
      ModuleCat.projective_of_module_projective _
    have : Module.Finite (X.presheaf.stalk x)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
      _root_.SheafOfModules.finite_stalk X.sheaf F x
    have hfree : Module.Free (X.presheaf.stalk x)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
      Module.free_of_flat_of_isLocalRing
    obtain ⟨V, hxV, r, ⟨e⟩⟩ := Scheme.Modules.exists_free_restrict_of_free_stalk F hF x hfree
    refine ⟨V, hxV, fun Y ι _ _ hι G _ k hk => ?_⟩
    refine subsingleton_zExt_of_iso
      (restrictLiftIso V ι hι F ≪≫
        (Scheme.Modules.restrictFunctor (liftToOpens V ι hι)).mapIso e ≪≫
          restrictFreeIso (liftToOpens V ι hι) (ULift.{u} (Fin r))) (Iso.refl _) k ?_
    exact subsingleton_zExt_free _ _ k (by omega)
  | m + 2, F, hF, x, h => by
    have : _root_.SheafOfModules.IsFiniteType F := hF.isFiniteType
    have hqc : F.IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
    obtain ⟨σ, hσ⟩ := Stacks.AmpleEventualGeneration.isFinGen_of_isAffine F hqc this
    let E : X.Modules := _root_.SheafOfModules.free σ.I
    let φ : E ⟶ F := F.freeHomEquiv.symm σ.s
    have : Epi φ := σ.epi
    let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ))
        inferInstance inferInstance
    have hE :
        _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.free (R := X.ringCatSheaf) σ.I) :=
      Stacks.AlgebraicGeometry.ProperMapping.isCoherent_sigma_modules _
        fun _ => Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
    have hK : _root_.SheafOfModules.IsCoherent (kernel φ) :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_kernel φ
    have hS' := hS.map_of_exact (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
    have hKx : HasProjectiveDimensionLT
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (kernel φ)) (m + 1) :=
      (hS'.hasProjectiveDimensionLT_X₃_iff m (projective_stalk_free x σ.I)).mp h
    obtain ⟨V, hxV, hV⟩ := extVanishesNear_of_hasProjectiveDimensionLT (m + 1) (kernel φ) hK x hKx
    refine ⟨V, hxV, fun Y ι _ _ hι G hG k hk => ?_⟩
    have hSι := Scheme.Modules.shortExact_map_restrictFunctor ι S hS
    refine subsingleton_hom_X₃_of_shortExact hSι _ k ?_ ?_
    · exact subsingleton_zExt_of_iso (restrictFreeIso ι σ.I) (Iso.refl _) k
        (subsingleton_zExt_free σ.I _ k (by omega))
    · exact hV Y ι hι G hG (k - 1) (by push_cast at hk ⊢; omega)

/-- **Vanishing of `Ext` near a point of a regular scheme, above the dimension of its local
ring.** If `X` is regular, `F` is coherent and `dim 𝒪_{X,x} ≤ c`, then there is an open
neighbourhood `V` of `x` with `Ext^k_W(F|_W, G|_W) = 0` for every affine open `W ⊆ V`, every
quasi-coherent `G` and every `k > c`. -/
theorem exists_nbhd_subsingleton_zExt {X : Scheme.{u}} (hX : IsRegular X) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (x : X) (c : ℕ) (hc : Order.coheight x ≤ c) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ W : X.Opens, IsAffineOpen W → W ≤ V → ∀ G : X.Modules,
      G.IsQuasicoherent → ∀ k : ℤ, (c : ℤ) < k →
        Subsingleton (Abelian.zExt (F.restrict W.ι) (G.restrict W.ι) k) := by
  have hLN : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  obtain ⟨U, hU, hxU, -⟩ : ∃ U : X.Opens, U ∈ X.affineOpens ∧ x ∈ U ∧ U ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsAffine U.toScheme := hU
  let x' : U.toScheme := ⟨x, hxU⟩
  have hreg : IsRegularLocalRing (U.toScheme.presheaf.stalk x') :=
    (hX.restrict U).isRegularLocalRing_stalk x'
  have hdim : ringKrullDim (U.toScheme.presheaf.stalk x') ≤ (c : WithBot ℕ∞) := by
    rw [ringKrullDim_stalk_eq_coheight, ← coheight_eq_of_isOpenImmersion U.ι]
    exact_mod_cast hc
  have hpd : HasProjectiveDimensionLT
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor U.toScheme x').obj (F.restrict U.ι))
      (c + 1) :=
    (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE hdim).2 _
  obtain ⟨V', hxV', hV'⟩ := extVanishesNear_of_hasProjectiveDimensionLT (c + 1) (F.restrict U.ι)
    (Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion U.ι F hF)
    x' hpd
  refine ⟨U.ι ''ᵁ V', ⟨x', hxV', rfl⟩, fun W hW hWV G hG k hk => ?_⟩
  have : IsAffine W.toScheme := hW
  have hWU : W ≤ U := fun w hw => by
    obtain ⟨v, -, rfl⟩ := hWV hw
    exact v.2
  have hWU' : Set.range W.ι.base ⊆ U := by
    rw [Scheme.Opens.range_ι]
    exact hWU
  let ι := liftToOpens U W.ι hWU'
  have hιU : ∀ w, U.ι.base (ι.base w) = W.ι.base w := fun w => by
    rw [← Scheme.Hom.comp_apply, liftToOpens_ι]
  have hι : Set.range ι.base ⊆ V' := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv, hv'⟩ := hWV (show W.ι.base w ∈ W from w.2)
    rw [← hιU] at hv'
    rwa [← U.ι.isOpenEmbedding.injective hv']
  exact subsingleton_zExt_of_iso (restrictLiftIso U W.ι hWU' F) (restrictLiftIso U W.ι hWU' G) k
    (hV' W.toScheme ι hι (G.restrict U.ι) inferInstance k (by push_cast; omega))

end Stacks.RegularExtVanishing

end
