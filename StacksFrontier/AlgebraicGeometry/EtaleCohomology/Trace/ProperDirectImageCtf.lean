module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.NoncommConstructibleFlatRepresentativeEtale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.EtaleModuleFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekInputs
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusCohomologyGap
public import StacksFrontier.Homology.DerivedCategory.RightDerivedInjectiveModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaCtf
public import StacksFrontier.Homology.TorAmplitude.BalancedTruncatedResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperDirectImageConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleBalancedTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange

/-!
# Proper direct image preserves `D_ctf` for a finite coefficient ring

Let `π : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian, and `Λ` a finite ring, not
necessarily commutative. This file proves that `Rπ_*` carries an object of `D^+(X_étale, Λ)` which
is `D_ctf` (`Stacks.EtaleCohomology.IsCtf`) to an object of `D^+(Y_étale, Λ)` which is `D_ctf`.
The input on constructibility is `Stacks.EtaleCohomology.LowerShriekConstructibilityInput`, Tag
0GL0, which is taken as a hypothesis here.

The proof runs as follows, after pulling back to an arbitrary quasi-compact and quasi-separated
`g : W ⟶ Y` of the big étale site and representing `K` by a complex `C` of constructible flat
sheaves concentrated in `[a, b]`:

1. *Constructibility.* The cohomology sheaves of `Rπ_* K`, with scalars restricted to `ℤ`, are
   constructible: restriction of scalars commutes with `Rπ_*`, and over `ℤ` this is Tag 0GL0
   applied to the constructible cohomology sheaves of `K`
   (`isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage`, in the
   namespace `Stacks.EtaleCohomology`). The cohomology sheaves of the inverse image to `W` are then
   constructible by Tag 095G (`Stacks.EtaleCohomology.isConstructibleEtaleModule_inverseImage`).
2. *Bounds.* `Rπ_*` raises the upper bound of the cohomology by at most a fixed `N`, on
   `D^+(X_étale, Λ)` and on `D^+_tors(X_étale, ℤ)` (part (3) of Tag 0G2A), so `Rπ_* K` has
   cohomology in `[a, b + N]`.
3. *Flatness.* By the noncommutative form of the construction of Tag 03TT
   (`Stacks.EtaleCohomology.isRepresentedByConstructibleFlatEtaleComplex_of_projective_cokernel`)
   it remains to see that, for a bounded above representative of `g^{-1} Rπ_* K` with finite
   projective stalks, the cokernel of the differential into degree `a` has projective stalks. By
   the module criterion
   `StacksDraft.TorAmplitude.projective_cokernel_of_isZero_homology_mapBifunctor` this follows
   from the vanishing of `H^{a-1}(Tot(R ⊗_Λ -))` on the stalks, for truncated finite free
   resolutions `R` of right `Λ`-modules of large length. This vanishing is proved on `Y`
   (`Stacks.EtaleCohomology.isZero_homology_mapBifunctor_stalk_directImage`): `Tot(R ⊗_Λ -)`
   commutes with `π_*` and with stalks, and carries an injective model of `C` to a complex of
   `π_*`-acyclic sheaves computing `Rπ_* Tot(R ⊗_Λ C)`, whose cohomology vanishes in a gap below
   `a` because the stalks of `C` are projective.

## Main results

* `Stacks.EtaleCohomology.isCtf_etaleModuleDerivedDirectImage_of_isProper` — proper direct image
  preserves `D_ctf`, given Tag 0GL0.
* `Stacks.EtaleCohomology.isZero_homology_mapBifunctor_stalk_directImage` — the vanishing of
  `H^{a-1}` of `Tot(R ⊗_Λ π_* J)` on stalks.

## References

* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u

namespace Stacks.EtaleCohomology

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits
  etaleModules_ab5OfSize

/-- **The stalk of an inverse image is the stalk at the image point**: for `g : W ⟶ Y` in a big
étale site and a geometric point `t` of `W`, `(g⁻¹F)_t ≅ F_{g(t)}`, naturally in `F`. -/
def etaleModuleInverseImageStalkIso (B : BigEtaleSite.{u}) {W Y : B.Scheme} (g : W ⟶ Y)
    (R : Type) [Ring R] (t : GeometricPoint W.obj) :
    etaleModuleInverseImage.{u, 0} R (B.inclusion.map g) ⋙ etaleModuleStalk.{u, 0} B W R t ≅
      etaleModuleStalk.{u, 0} B Y R (t.map (B.inclusion.map g)) :=
  ((Scheme.pointSmallEtale t.hom).sheafFiberComapIso (smallEtaleBaseChange (B.inclusion.map g))
      (coverPreserving_smallEtaleBaseChange (B.inclusion.map g)) (ModuleCat.{u + 1} R)).symm ≪≫
    (GrothendieckTopology.Point.sheafFiberIsoOfFiberIso (A := ModuleCat.{u + 1} R)
      (Scheme.pointSmallEtale (t.hom ≫ B.inclusion.map g))
      ((Scheme.pointSmallEtale t.hom).comap (smallEtaleBaseChange (B.inclusion.map g))
        (coverPreserving_smallEtaleBaseChange (B.inclusion.map g)))
      (pointSmallEtaleComapFiberIso (B.inclusion.map g) t.hom)).symm

/-- `Tot(R ⊗_Λ -)` preserves and reflects the vanishing of homology along a
quasi-isomorphism, for a truncated finite free resolution `R`. -/
theorem isZero_homology_mapBifunctor_iff_of_quasiIso_right (Λ : Type) [Ring Λ]
    {R : CochainComplex (ModuleCat.{u + 1} Λᵐᵒᵖ) ℤ} {m : ℕ}
    (hR : StacksDraft.TorAmplitude.IsTruncatedFreeResolution R m)
    {E₁ E₂ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ} (f : E₁ ⟶ E₂) [QuasiIso f] (n : ℤ) :
    IsZero ((HomologicalComplex.mapBifunctor R E₁ (StacksDraft.Perfect.balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology n) ↔
      IsZero ((HomologicalComplex.mapBifunctor R E₂ (StacksDraft.Perfect.balancedTensorFunctor Λ)
        (ComplexShape.up ℤ)).homology n) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := hR
  have := fun q => (h₃ q).1
  have := fun q => (h₃ q).2
  have := StacksDraft.Perfect.quasiIso_mapBifunctorMap_balancedTensorFunctor Λ R (-(m : ℤ)) 0 f
  exact StacksDraft.TorAmplitude.isZero_homology_iff_of_quasiIso
    (HomologicalComplex.mapBifunctorMap (𝟙 R) f (StacksDraft.Perfect.balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)) n

/-- A functor preserving zero morphisms preserves complexes concentrated in degrees `≥ a`. -/
private theorem isStrictlyGE_map_obj {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyGE a i hi)

/-- A functor preserving zero morphisms preserves complexes concentrated in degrees `≤ b`. -/
private theorem isStrictlyLE_map_obj {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (b : ℤ)
    [K.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyLE b i hi)

/-- `Tot(R ⊗_Λ C)` is killed by `Nat.card Λ`, for a finite ring `Λ`. -/
private theorem nsmul_card_id_etaleModuleBalancedTensorTotal (Λ : Type) [Ring Λ] [Finite Λ]
    {X : Scheme.{u}} (R : CochainComplex (ModuleCat.{u + 1} Λᵐᵒᵖ) ℤ)
    (C : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :
    Nat.card Λ • 𝟙 (etaleModuleBalancedTensorTotal R C) = 0 := by
  have := Fintype.ofFinite Λ
  have hC0 : ∀ p, Nat.card Λ • 𝟙 (C.X p) = 0 := fun p => by
    ext U x
    change Nat.card Λ • x = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero, zero_smul]
  ext k : 1
  refine HomologicalComplex.mapBifunctor.hom_ext (fun q p h => ?_)
  have h0 : Nat.card Λ • 𝟙 (((etaleModuleBalancedTensor Λ X).obj (R.X q)).obj (C.X p)) = 0 := by
    rw [← ((etaleModuleBalancedTensor Λ X).obj (R.X q)).map_id (C.X p), ← Functor.map_nsmul,
      hC0 p, Functor.map_zero]
  let ι := HomologicalComplex.ιMapBifunctor R C (etaleModuleBalancedTensor Λ X)
    (ComplexShape.up ℤ) q p k h
  have e1 : ι ≫ (Nat.card Λ • 𝟙 (etaleModuleBalancedTensorTotal R C)).f k = Nat.card Λ • ι :=
    (Preadditive.comp_nsmul ι (𝟙 _) _).trans (congrArg _ (Category.comp_id ι))
  have e2 : (Nat.card Λ • 𝟙 (((etaleModuleBalancedTensor Λ X).obj (R.X q)).obj (C.X p))) ≫
      ι = Nat.card Λ • ι :=
    (Preadditive.nsmul_comp _ _ _).trans (congrArg _ (Category.id_comp ι))
  rw [e1, ← e2, h0, zero_comp, HomologicalComplex.zero_f]
  exact comp_zero.symm

/-- For a truncated finite free resolution `R` of length `m` and a complex `C` concentrated in
`[a, b]` with projective stalks, `Tot(R ⊗_Λ C)` has no cohomology in degrees `(b - m, a)`. -/
private theorem isZero_homology_etaleModuleBalancedTensorTotal_of_projective_stalks {X : Scheme.{u}}
    (Λ : Type) [Ring Λ] (C : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (hC : ∀ (n : ℤ) (x : GeometricPoint X),
      Module.Projective Λ (((Scheme.pointSmallEtale x.hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj (C.X n)))
    {R : CochainComplex (ModuleCat.{u + 1} Λᵐᵒᵖ) ℤ} {m : ℕ}
    (hR : StacksDraft.TorAmplitude.IsTruncatedFreeResolution R m) (p : ℤ) (hp₁ : b - m < p)
    (hp₂ : p < a) : IsZero ((etaleModuleBalancedTensorTotal R C).homology p) := by
  rw [isZero_homology_etaleModuleBalancedTensorTotal_iff]
  intro x
  let Sx := (Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have := isStrictlyGE_map_obj Sx C a
  have := isStrictlyLE_map_obj Sx C b
  exact StacksDraft.TorAmplitude.isZero_homology_mapBifunctor_of_projective hR _ a b
    (fun n => hC n x) p hp₁ hp₂

/-- The stalks of a constructible flat sheaf of `Λ`-modules are projective `Λ`-modules. -/
private theorem module_projective_sheafFiber_of_isConstructibleFlatEtaleModule
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsConstructibleFlatEtaleModule B X Λ F) (x : GeometricPoint X.obj) :
    Module.Projective Λ (((Scheme.pointSmallEtale x.hom).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) := by
  have : Module.Projective Λ ((etaleModulesToSmallEtale B X Λ ⋙
      etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ x).obj F) :=
    etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ _ hF x
  exact Module.Projective.of_equiv'
    ((etaleModuleStalkIsoTransport.{u, 0} B X Λ x).app F).symm.toLinearEquiv

/-- **The vanishing on the target.** Let `π : X ⟶ Y` have cohomological amplitude `N` on
torsion sheaves of abelian groups, `C` a complex of sheaves of `Λ`-modules concentrated in
`[a, b]` with projective stalks, and `C ⟶ J` an injective resolution. For a truncated finite
free resolution `R` of length `m ≥ b + N - a + 2`, the stalks of `Tot(R ⊗_Λ π_* J)` have no
cohomology in degree `a - 1`: `π_* Tot(R ⊗_Λ J)` computes `Rπ_* Tot(R ⊗_Λ C)`, whose cohomology
sheaves vanish in `(b - m, a)` (the stalks of `C` being projective), and the amplitude bound
carries this gap to `H^{a-1}`. -/
theorem isZero_homology_mapBifunctor_stalk_directImage {X Y : Scheme.{u}} (π : X ⟶ Y)
    (Λ : Type) [Ring Λ] [Finite Λ]
    (C : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (a b : ℤ) [C.IsStrictlyGE a]
    [C.IsStrictlyLE b]
    (hC : ∀ (n : ℤ) (x : GeometricPoint X),
      Module.Projective Λ (((Scheme.pointSmallEtale x.hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj (C.X n)))
    (Jc : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) [Jc.IsStrictlyGE a]
    [∀ p, Injective (Jc.X p)] (iJ : C ⟶ Jc) (hiJ : QuasiIso iJ) (N : ℕ)
    (hN : ∀ L : DerivedCategory.Plus (EtaleModules.{u, 0} ℤ X), isTorsionPlus.{u, 0} ℤ X L →
      ∀ c : ℤ, (DerivedCategory.Plus.ι.obj L).IsLE c →
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} ℤ π).obj L)).IsLE
          (c + N))
    (R : CochainComplex (ModuleCat.{u + 1} Λᵐᵒᵖ) ℤ) (m : ℕ)
    (hR : StacksDraft.TorAmplitude.IsTruncatedFreeResolution R m)
    (hm : b + N - a + 2 ≤ (m : ℤ)) (y : GeometricPoint Y) :
    IsZero ((HomologicalComplex.mapBifunctor R
      ((((Scheme.pointSmallEtale y.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Jc)) (StacksDraft.Perfect.balancedTensorFunctor Λ)
          (ComplexShape.up ℤ)).homology (a - 1)) := by
  have hR' := hR
  obtain ⟨hR₁, hR₂, hR₃, -⟩ := hR
  have : R.IsStrictlyGE (-(m : ℤ)) := hR₁
  have : R.IsStrictlyLE 0 := hR₂
  have := fun q => (hR₃ q).1
  have := fun q => (hR₃ q).2
  let G := etaleModuleDirectImage.{u, 0} ℤ π
  let L := etaleModuleBalancedTensorTotal R Jc
  let L₀ := etaleModuleBalancedTensorTotal R C
  have hGE : ∀ (D : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ), D.IsStrictlyGE a →
      CochainComplex.IsStrictlyGE (etaleModuleBalancedTensorTotal R D) (-(m : ℤ) + a) :=
    fun D _ => (CochainComplex.isStrictlyGE_iff _ _).2 fun n hn =>
      StacksDraft.TorAmplitude.isZero_mapBifunctor_X_of_isStrictlyGE
        (etaleModuleBalancedTensor Λ X) R D (-(m : ℤ)) a n hn
  have : CochainComplex.IsStrictlyGE L (-(m : ℤ) + a) := hGE Jc inferInstance
  have : CochainComplex.IsStrictlyGE L₀ (-(m : ℤ) + a) := hGE C inferInstance
  let Lp : CochainComplex.Plus (EtaleModules.{u, 0} ℤ X) := ⟨L, ⟨-(m : ℤ) + a, inferInstance⟩⟩
  let L₀p : CochainComplex.Plus (EtaleModules.{u, 0} ℤ X) := ⟨L₀, ⟨-(m : ℤ) + a, inferInstance⟩⟩
  -- reduce to the vanishing of a homology sheaf on `Y`
  suffices hkey : IsZero ((etaleModuleBalancedTensorTotal R
      (((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        Jc)).homology (a - 1)) from
    (isZero_homology_etaleModuleBalancedTensorTotal_iff R _ (a - 1)).1 hkey y
  suffices hkey' : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology (a - 1))
    from hkey'.of_iso (HomologicalComplex.homologyMapIso
      (etaleModuleBalancedTensorTotalDirectImageIso R π Jc (-(m : ℤ)) 0).symm (a - 1))
  -- `π_* L` computes `Rπ_* L`
  have hacyc := Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic G
    ((HomotopyCategory.Plus.quotient _).obj Lp)
    (fun n => rightAcyclic_etaleModuleBalancedTensorTotal_X R π (-(m : ℤ)) 0 Jc n)
  let eU : DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj Lp) ≅
      G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L₀p) :=
    (Stacks.InjectiveModel.plusQhIsoPlusQ (G.mapCochainComplexPlus.obj Lp)).symm ≪≫
      @asIso _ _ _ _ _ hacyc ≪≫
      G.rightDerivedFunctorPlus.mapIso (Stacks.InjectiveModel.plusQhIsoPlusQ Lp ≪≫
        (by
          have : QuasiIso (etaleModuleBalancedTensorTotalMap R iJ) :=
            quasiIso_etaleModuleBalancedTensorTotalMap R (-(m : ℤ)) 0 iJ
          have hqi : IsIso (DerivedCategory.Q.map (etaleModuleBalancedTensorTotalMap R iJ)) :=
            (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
          exact (DerivedCategory.Plus.ι.preimageIso (X := DerivedCategory.Plus.Q.obj L₀p)
            (Y := DerivedCategory.Plus.Q.obj Lp)
            (@asIso _ _ _ _ _ hqi)).symm))
  refine (?_ : IsZero ((DerivedCategory.Plus.homologyFunctor _ (a - 1)).obj
      (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L₀p)))).of_iso
    (((DerivedCategory.homologyFunctorFactors _ (a - 1)).app _).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ (a - 1)).mapIso eU)
  -- the gap
  let P : ObjectProperty (EtaleModules.{u, 0} ℤ X) := fun F => IsTorsionEtaleModule.{u, 0} ℤ X F
  have : P.ContainsZero := ⟨⟨0, isZero_zero _, isTorsionEtaleModule_of_isZero ℤ X (isZero_zero _)⟩⟩
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h => IsTorsionEtaleModule.of_iso ℤ X e h⟩
  refine Functor.isZero_homology_rightDerivedFunctorPlus_of_gap G P N (fun K c hK hc => ?_) _ ?_ a
    (b - m) ?_ (by omega)
  · exact (DerivedCategory.Plus.isLE_ι_obj_iff _ _).1
      (hN K hK c ((DerivedCategory.Plus.isLE_ι_obj_iff K c).2 hc))
  · refine isTorsionPlus_of_nsmul_id_eq_zero _ (Nat.card Λ) Nat.card_pos ?_
    -- every term of `C` is killed by `#Λ`, hence so is `Tot(R ⊗_Λ C)`
    have h' : Nat.card Λ • 𝟙 L₀p = 0 :=
      ObjectProperty.hom_ext _ (nsmul_card_id_etaleModuleBalancedTensorTotal Λ R C)
    rw [← DerivedCategory.Plus.Q.map_id, ← Functor.map_nsmul, h', Functor.map_zero]
  · intro p hp₁ hp₂
    refine (?_ : IsZero (L₀.homology p)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ p).app L₀)
    exact isZero_homology_etaleModuleBalancedTensorTotal_of_projective_stalks Λ C a b hC hR' p
      hp₁ hp₂

/-- **Proper direct image preserves `D_ctf`**, for a finite, not necessarily commutative, ring
`Λ`. Let `π : X ⟶ Y` be proper with `Y` Noetherian, both in the big étale site `B`. If `K` in
`D^+(X_étale, Λ)` is `D_ctf`, so is `Rπ_* K` in `D^+(Y_étale, Λ)`.

The hypothesis `hC` is Stacks Tag 0GL0 (`LowerShriekConstructibilityInput`): it is the only
Stacks result taken as a hypothesis. It is applied at
`Λ = ℤ`, the noncommutative case being reduced to constructibility over `ℤ` by restriction of
scalars. This is an intermediate lemma, not the registration of a Stacks tag. -/
theorem isCtf_etaleModuleDerivedDirectImage_of_isProper
    (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [IsNoetherian Y]
    (hX : B.Contains X) (hY : B.Contains Y) (Λ : Type) [Ring Λ] [Finite Λ]
    (hC : LowerShriekConstructibilityInput B)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Plus.ι.obj K)) :
    IsCtf B (B.obj Y hY) Λ
      (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)) := by
  have hYc : CompactSpace Y := IsNoetherian.toCompactSpace
  have hYq : QuasiSeparatedSpace Y :=
    @IsLocallyNoetherian.quasiSeparatedSpace Y IsNoetherian.toIsLocallyNoetherian
  have hπs : IsSeparated π := IsProper.toIsSeparated
  have hπu : UniversallyClosed π := IsProper.toUniversallyClosed
  have hπq : QuasiSeparated π := IsSeparated.instQuasiSeparated π
  have hπc : QuasiCompact π := instQuasiCompactOfUniversallyClosed π
  have hXc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have hXq : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  have hXc' : CompactSpace (B.obj X hX).obj := hXc
  have hXq' : QuasiSeparatedSpace (B.obj X hX).obj := hXq
  obtain ⟨C, a, b, hCa, hCb, hCflat, ⟨eC⟩⟩ := (isCtf_iff_of_qcqs B Λ _).1 hK
  obtain ⟨NΛ, hNΛ⟩ := exists_isLE_etaleModuleDerivedDirectImage_of_isProper π Λ
  obtain ⟨Nℤ, hNℤ⟩ := exists_isLE_etaleModuleDerivedDirectImage_of_isProper_of_isTorsionPlus π ℤ
  set N : ℕ := max NΛ Nℤ with hNdef
  -- the bounds of `M = Rπ_* K`
  have hMGE : (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)).IsGE a := by
    have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).1
      (DerivedCategory.TStructure.t.isGE_of_iso eC a)
    exact (DerivedCategory.Plus.isGE_ι_obj_iff _ a).2
      (Functor.isGE_rightDerivedFunctorPlus_obj (etaleModuleDirectImage.{u, 0} Λ π) K a)
  have hMLE : (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)).IsLE (b + N) := by
    have := hNΛ K b (DerivedCategory.TStructure.t.isLE_of_iso eC b)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b + NΛ) (b + N) (by omega)
  -- an injective model `J` of `K`, receiving a quasi-isomorphism from `C`
  obtain ⟨J, hJa, iJ, hiJ⟩ := CochainComplex.Plus.exists_quasiIso_injective
    (C := EtaleModules.{u, 0} Λ X) ⟨C, ⟨a, inferInstance⟩⟩ a
  have hiJ' : QuasiIso iJ.hom := hiJ
  let Jc := ((InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J.obj
  have eKJ : DerivedCategory.Plus.Q.obj
      ((InjectiveObject.ι _).mapCochainComplexPlus.obj J) ≅ K :=
    DerivedCategory.Plus.ι.preimageIso
      ((asIso (DerivedCategory.Q.map iJ.hom)).symm ≪≫ eC)
  have eMJ : DerivedCategory.Q.obj (((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Jc) ≅
        DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K) :=
    DerivedCategory.Plus.ι.mapIso ((Stacks.InjectiveModel.plusQhIsoPlusQ
      ((etaleModuleDirectImage.{u, 0} Λ π).mapCochainComplexPlus.obj
        ((InjectiveObject.ι _).mapCochainComplexPlus.obj J))).symm ≪≫
      Stacks.InjectiveModel.rightDerivedFunctorPlusUnitIso _ J ≪≫
      (etaleModuleDirectImage.{u, 0} Λ π).rightDerivedFunctorPlus.mapIso
        (Stacks.InjectiveModel.plusQhIsoPlusQ
          ((InjectiveObject.ι _).mapCochainComplexPlus.obj J) ≪≫ eKJ))
  intro W g hWc hWq
  let G := etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map g)
  let M := DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)
  refine isRepresentedByConstructibleFlatEtaleComplex_of_projective_cokernel B W Λ _ a (b + N)
    ?_ ?_ ?_
  · intro i
    have hMcons : IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
          ((DerivedCategory.homologyFunctor _ i).obj M)) :=
      isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage B π hX hY Λ
        hC K hK i
    have := isWeakSerreClass_isBigSiteConstructibleEtaleModule.{u, 0} B W ℤ
    refine (IsBigSiteConstructibleEtaleModule B W ℤ).prop_of_iso
      (((etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ) (B.inclusion.map g)).app
          ((DerivedCategory.homologyFunctor _ i).obj M)) ≪≫
        (etaleModuleRestrictScalars (Int.castRingHom Λ) W.obj).mapIso
          ((G.mapDerivedCategoryHomologyIso i).app M).symm)
      (isConstructibleEtaleModule_inverseImage B ℤ g hMcons)
  · intro i hi
    refine (G.map_isZero ?_).of_iso ((G.mapDerivedCategoryHomologyIso i).app M)
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE M a i hi
    · exact DerivedCategory.isZero_of_isLE M (b + N) i hi
  · intro Y' ⟨eY'⟩ _ hfin s
    let St := etaleModuleStalk.{u, 0} B W Λ s
    let E := (St.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y'
    have hEb : CochainComplex.IsStrictlyLE E (b + N) := isStrictlyLE_map_obj St Y' (b + N)
    have hY'n : ∀ n < a, Y'.ExactAt n := fun n hn =>
      (HomologicalComplex.exactAt_iff_isZero_homology Y' n).2
        ((((G.map_isZero (DerivedCategory.isZero_of_isGE M a n hn)).of_iso
          ((G.mapDerivedCategoryHomologyIso n).app M)).of_iso
          ((DerivedCategory.homologyFunctor _ n).mapIso eY')).of_iso
          ((DerivedCategory.homologyFunctorFactors _ n).app Y').symm)
    -- `Y'` is quasi-isomorphic to the bounded below complex `Y₁ = τ_{≥ a} Y'`
    have : Y'.IsGE a := by
      rw [CochainComplex.isGE_iff]
      exact hY'n
    let Y₁ : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.obj) := ⟨Y'.truncGE a, ⟨a, inferInstance⟩⟩
    -- the model `D₁ = g⁻¹ π_* J` of `K'`
    let D₀ := ((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex (ComplexShape.up ℤ)).obj Jc
    let D₁ : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.obj) :=
      G.mapCochainComplexPlus.obj ((etaleModuleDirectImage.{u, 0} Λ π).mapCochainComplexPlus.obj
        ((InjectiveObject.ι _).mapCochainComplexPlus.obj J))
    have eY₁D₁ : DerivedCategory.Q.obj Y₁.obj ≅ DerivedCategory.Q.obj D₁.obj :=
      (asIso (DerivedCategory.Q.map (Y'.πTruncGE a))).symm ≪≫ eY' ≪≫
        G.mapDerivedCategory.mapIso eMJ.symm ≪≫ G.mapDerivedCategoryFactors.app D₀
    obtain ⟨I', sI, tI, hsI, htI⟩ := CochainComplex.exists_quasiIso_zigzag_of_Q_iso Y₁ D₁ eY₁D₁
    have hcok : (cokernel (E.d (a - 1) a) : ModuleCat.{u + 1} Λ) ≅
        St.obj (cokernel (Y'.d (a - 1) a)) :=
      (PreservesCokernel.iso St (Y'.d (a - 1) a)).symm
    have hproj : Module.Projective Λ (cokernel (E.d (a - 1) a) : ModuleCat.{u + 1} Λ) :=
      StacksDraft.TorAmplitude.projective_cokernel_of_isZero_homology_mapBifunctor E a (b + N)
        (fun n => hfin n s) (fun R m hm hR => by
          have hYs : IsZero ((HomologicalComplex.mapBifunctor R
              ((etaleModuleStalk.{u, 0} B (B.obj Y hY) Λ
                  (s.map (B.inclusion.map g))).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj D₀) (StacksDraft.Perfect.balancedTensorFunctor Λ)
              (ComplexShape.up ℤ)).homology (a - 1)) := by
            have : CochainComplex.IsStrictlyGE Jc a :=
              isStrictlyGE_map_obj (InjectiveObject.ι _) J.obj a
            have : ∀ p, Injective (Jc.X p) := fun p => by
              dsimp [Jc]
              infer_instance
            refine isZero_homology_mapBifunctor_stalk_directImage π Λ C a b (fun n x => ?_) Jc
              iJ.hom hiJ' N (fun L hL c hc => ?_) R m hR hm (s.map (B.inclusion.map g))
            · exact module_projective_sheafFiber_of_isConstructibleFlatEtaleModule B (B.obj X hX) Λ
                _ (hCflat n) x
            · have := hNℤ L hL c hc
              exact DerivedCategory.TStructure.t.isLE_of_le _ (c + Nℤ) (c + N) (by omega)
          -- transport along the zigzag and the stalk of the inverse image
          have := etaleModuleStalk_additive.{u, 0} B W Λ s
          have := etaleModuleStalk_additive.{u, 0} B (B.obj Y hY) Λ (s.map (B.inclusion.map g))
          let eD : (St.mapHomologicalComplex (ComplexShape.up ℤ)).obj D₁.obj ≅
              (etaleModuleStalk.{u, 0} B (B.obj Y hY) Λ
                  (s.map (B.inclusion.map g))).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj D₀ :=
            (Functor.mapHomologicalComplexCompIso (etaleModuleInverseImageStalkIso B g Λ s)
              (ComplexShape.up ℤ)).app D₀
          exact (isZero_homology_mapBifunctor_iff_of_quasiIso_right Λ hR
            ((St.mapHomologicalComplex (ComplexShape.up ℤ)).map (Y'.πTruncGE a)) (a - 1)).2
            ((isZero_homology_mapBifunctor_iff_of_quasiIso_right Λ hR
              ((St.mapHomologicalComplex (ComplexShape.up ℤ)).map sI.hom) (a - 1)).2
            ((isZero_homology_mapBifunctor_iff_of_quasiIso_right Λ hR
              ((St.mapHomologicalComplex (ComplexShape.up ℤ)).map tI.hom) (a - 1)).1
            ((isZero_homology_mapBifunctor_iff_of_quasiIso_right Λ hR eD.hom (a - 1)).2 hYs))))
    exact Module.Projective.of_equiv' hcok.toLinearEquiv

end Stacks.EtaleCohomology

end
