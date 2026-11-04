module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankStratumExistence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibresAffineConverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEComparison
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# Base change for the bottom cohomology on the bottom rank stratum

Let `K` be an object of `D(𝒪_Z)` with no cohomology below degree `a`, and let
`τ^{≤a} K ⟶ K ⟶ τ^{≥a+1} K` be its truncation triangle. If for a morphism `g : Y ⟶ Z` the derived
pullback `Lg^* τ^{≥a+1} K` still has no cohomology in degrees `≤ a`, then
`H^a(Lg^* K) ≅ g^* H^a(K)`: the long exact cohomology sequence identifies `H^a(Lg^* K)` with
`H^a(Lg^* τ^{≤a} K)`, and `τ^{≤a} K` is the module `H^a(K)` placed in degree `a`, whose derived
pullback has `g^* H^a(K)` as its top cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

/-- In a distinguished triangle whose third vertex has no cohomology in degrees `≤ n`, the first
morphism is an isomorphism on cohomology in degree `n`. -/
theorem isIso_homologyMap_mor₁_of_isGE {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) (n : ℤ)
    (h : T.obj₃.IsGE (n + 1)) :
    IsIso ((DerivedCategory.homologyFunctor C n).map T.mor₁) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor C n).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n (by omega)).2
      ((DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) (n - 1) (by omega)).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor C n).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n).2
      ((DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) n (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules) (a : ℤ)

/-- **Base change for the bottom cohomology, from a bound on the pulled back truncation.** Let
`j : Z ⟶ X` be such that `K = Lj^* E` has no cohomology below `a`. If `g : Y ⟶ Z` pulls the
truncation `τ^{≥a+1} K` back to an object with no cohomology in degrees `≤ a`, then
`H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)`. -/
theorem nonempty_pullbackHomology_comp_iso {Z Y : Scheme.{u}} (j : Z ⟶ X)
    (hK : ((derivedPullback j.toLRSHom.toShHom).obj E).IsGE a) (g : Y ⟶ Z)
    (hg : ((derivedPullback g.toLRSHom.toShHom).obj
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj
        ((derivedPullback j.toLRSHom.toShHom).obj E))).IsGE (a + 1)) :
    Nonempty (pullbackHomology E a (g ≫ j) ≅
      (Scheme.Modules.pullback g).obj (pullbackHomology E a j)) := by
  set K := (derivedPullback j.toLRSHom.toShHom).obj E
  set T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj K
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLEGE_distinguished _ _ rfl K
  have hT₃ : T.obj₃.IsGE (a + 1) :=
    (inferInstance : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1))
  have h₁ : ∀ i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
    fun i hi => isIso_homologyMap_mor₁_of_isGE T hT i
      (DerivedCategory.TStructure.t.isGE_of_ge _ (i + 1) (a + 1) (by omega))
  have hle : T.obj₁.IsLE a :=
    (inferInstance : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLE a).obj K) a)
  have hge : T.obj₁.IsGE a :=
    (DerivedCategory.isGE_iff _ _).2 fun i hi => (DerivedCategory.isZero_of_isGE K a i hi).of_iso
      (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ i).map T.mor₁) (h₁ i (by omega)))
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₁ a
  have hg' := isIso_homologyMap_mor₁_of_isGE _
    ((derivedPullback g.toLRSHom.toShHom).map_distinguished T hT) a hg
  exact ⟨(pullbackHomologyCompIso E a g j).symm ≪≫
    (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ a).map
      ((derivedPullback g.toLRSHom.toShHom).map T.mor₁)) hg').symm ≪≫
    (DerivedCategory.homologyFunctor _ a).mapIso ((derivedPullback g.toLRSHom.toShHom).mapIso e) ≪≫
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso
      g.toLRSHom.toShHom M a ≪≫
    (Scheme.Modules.pullback g).mapIso
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ a).app M).symm ≪≫
        (DerivedCategory.homologyFunctor _ a).mapIso e.symm ≪≫
        @asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ a).map T.mor₁) (h₁ a le_rfl))⟩

/-! ### Bounds below for derived pullbacks -/

/-- **A bounded complex of flat modules concentrated in degrees `≥ n` stays so under every
derived pullback.** It is K-flat ([stacks 06YQ]), so it computes the derived pullback
([stacks 06YJ]), and degreewise pullback preserves vanishing in degrees `< n`. -/
theorem isGE_derivedPullback_Q_obj_of_isFlat {W Y : Scheme.{u}} (g : Y ⟶ W)
    (F : CochainComplex W.Modules ℤ) (m n : ℤ) [CochainComplex.IsStrictlyLE F m]
    [CochainComplex.IsStrictlyGE F n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf)
      (F.X i)) :
    ((derivedPullback g.toLRSHom.toShHom).obj (DerivedCategory.Q.obj F)).IsGE n := by
  have hK : RingedSpace.KFlatDerivedPullback.KFlat W.toRingedSpace F :=
    RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat _ F
      ⟨m, (CochainComplex.isStrictlyLE_iff F m).2 fun i hi => F.isZero_of_isStrictlyLE m i hi⟩
      hflat
  have hiso := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    g.toLRSHom.toShHom F hK
  let L := ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj F
  have hL : CochainComplex.IsStrictlyGE L n :=
    (CochainComplex.isStrictlyGE_iff L n).2 fun i hi =>
      Functor.map_isZero _ (F.isZero_of_isStrictlyGE n i hi)
  have e₁ : (derivedPullback g.toLRSHom.toShHom).obj (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj L :=
    (derivedPullback g.toLRSHom.toShHom).mapIso
        ((DerivedCategory.quotientCompQhIso _).app F).symm ≪≫
      @asIso _ _ _ _ ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        g.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)) hiso ≪≫
      (DerivedCategory.quotientCompQhIso _).app L
  exact DerivedCategory.TStructure.t.isGE_of_iso e₁.symm n

/-- Restricting the `i`-th cohomology of `L` to an open is zero iff the `i`-th cohomology of its
derived pullback along the open immersion is. -/
private theorem isZero_restrict_homology_iff {W Y : Scheme.{u}} (w : W ⟶ Y) [IsOpenImmersion w]
    (L : DerivedCategory Y.Modules) (i : ℤ) :
    IsZero ((Scheme.Modules.restrictFunctor w).obj
        ((DerivedCategory.homologyFunctor _ i).obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedPullback w.toLRSHom.toShHom).obj L)) :=
  Iso.isZero_iff
    (((Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso w i).app L).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (derivedRestrictObjIso w L).symm)

/-- **Being bounded below is local along open immersions.** -/
theorem isGE_of_forall_exists_openImmersion {Y : Scheme.{u}} (L : DerivedCategory Y.Modules)
    (n : ℤ) (h : ∀ y : Y, ∃ (W : Scheme.{u}) (ι : W ⟶ Y) (_ : IsOpenImmersion ι),
      y ∈ Set.range ι.base ∧ ((derivedPullback ι.toLRSHom.toShHom).obj L).IsGE n) :
    L.IsGE n := by
  choose W ι hι hy hL using h
  refine (DerivedCategory.isGE_iff _ _).2 fun i hi => ?_
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover
    (fun y => (ι y).opensRange) (eq_top_iff.2 fun y _ =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) _ fun y => ?_
  have hz := (isZero_restrict_homology_iff (ι y) L i).2
    ((DerivedCategory.isGE_iff _ n).1 (hL y) i hi)
  exact ((Scheme.Modules.restrictFunctor (ι y).isoOpensRange.inv).map_isZero hz).of_iso
    ((Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (ι y)).symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp (ι y).isoOpensRange.inv (ι y)).app _)

/-- Derived pullback along an open immersion preserves boundedness below: it is restriction,
which is exact. -/
theorem isGE_derivedPullback_of_isOpenImmersion {W Y : Scheme.{u}} (w : W ⟶ Y) [IsOpenImmersion w]
    (L : DerivedCategory Y.Modules) (n : ℤ) (hL : L.IsGE n) :
    ((derivedPullback w.toLRSHom.toShHom).obj L).IsGE n :=
  (DerivedCategory.isGE_iff _ _).2 fun i hi =>
    (isZero_restrict_homology_iff w L i).1 ((Scheme.Modules.restrictFunctor w).map_isZero
      (DerivedCategory.isZero_of_isGE L n i hi))

/-- **Truncation commutes with restriction to an open.** For an open immersion `w`,
`Lw^* τ^{≥n} K ≅ τ^{≥n} Lw^* K`: the derived pullback of the truncation triangle of `K` is a
distinguished triangle with first vertex `≤ n - 1` and third vertex `≥ n`, and such a triangle is
unique. -/
theorem nonempty_derivedPullback_truncGE_iso {W Y : Scheme.{u}} (w : W ⟶ Y) [IsOpenImmersion w]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))) (n : ℤ) :
    Nonempty ((derivedPullback w.toLRSHom.toShHom).obj
        ((DerivedCategory.TStructure.t.truncGE n).obj K) ≅
      (DerivedCategory.TStructure.t.truncGE n).obj
        ((derivedPullback w.toLRSHom.toShHom).obj K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE n).obj K
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished n K
  have hT₁ := (derivedPullback w.toLRSHom.toShHom).map_distinguished T hT
  have hT₂ := DerivedCategory.TStructure.t.triangleLTGE_distinguished n
    ((derivedPullback w.toLRSHom.toShHom).obj K)
  have h₀ : ((derivedPullback w.toLRSHom.toShHom).obj T.obj₁).IsLE (n - 1) :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj w.toLRSHom.toShHom
      T.obj₁ (n - 1) (inferInstanceAs (DerivedCategory.TStructure.t.IsLE
        ((DerivedCategory.TStructure.t.truncLT n).obj K) (n - 1)))
  have h₁ : ((derivedPullback w.toLRSHom.toShHom).obj T.obj₃).IsGE n :=
    isGE_derivedPullback_of_isOpenImmersion w T.obj₃ n
      (inferInstanceAs (DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE n).obj K) n))
  obtain ⟨e, -⟩ := DerivedCategory.TStructure.t.triangle_iso_exists hT₁ hT₂
    (Iso.refl _) (n - 1) n h₀ h₁
    (inferInstanceAs (DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT n).obj
        ((derivedPullback w.toLRSHom.toShHom).obj K)) (n - 1)))
    (inferInstanceAs (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE n).obj
        ((derivedPullback w.toLRSHom.toShHom).obj K)) n))
  exact ⟨Triangle.π₃.mapIso e⟩

/-- The sheaf associated to a flat module is flat, at the spelling of the K-flat criterion. -/
theorem isFlat_tilde_of_flat {T : CommRingCat.{u}} (M : ModuleCat.{u} T) [Module.Flat T M] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (Spec T).sheaf)
      ((tilde.functor T).obj M) :=
  (isFlat_tilde_iff_flat M).2 inferInstance

/-- The terms of the canonical truncation above degree `n` of a complex of flat modules whose
differential into degree `n` vanishes are flat. -/
theorem isFlat_truncGE_X {W : Scheme.{u}} (F₀ : CochainComplex W.Modules ℤ) (n : ℤ)
    (hF₀ : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf) (F₀.X i))
    (hd : F₀.d (n - 1) n = 0) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf)
      ((CochainComplex.truncGE F₀ n).X i) := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_isZero _
      (CochainComplex.isZero_of_isStrictlyGE (CochainComplex.truncGE F₀ n) n i hi)
  · exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
      (@asIso _ _ _ _ (F₀.pOpcycles i) (F₀.isIso_pOpcycles (i - 1) i (by simp) hd) ≪≫
        (CochainComplex.truncGEXIsoOpcycles F₀ i).symm) (hF₀ i)
  · exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
      (CochainComplex.truncGEXIso F₀ n i hi).symm (hF₀ i)

/-- Truncation of a complex of sheaves above degree `n` represents the truncation in the derived
category. -/
def truncGEQIso {W : Scheme.{u}} (F₀ : CochainComplex W.Modules ℤ) (n : ℤ) :
    (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj F₀) ≅
      DerivedCategory.Q.obj (CochainComplex.truncGE F₀ n) :=
  @asIso _ _ _ _ _ (DerivedCategory.isIso_descTruncGE_Q_map_πTruncGE F₀ n)

/-- **On an affine chart where the bottom differential vanishes, every derived pullback of the
truncation above the bottom degree stays above it.** Let `L` on `Spec T` be the derived
sheafification of a bounded complex `P` of free modules whose differential out of degree `a`
is zero. Then `τ^{≥a+1} L` is the canonical truncation of the sheafified complex, a bounded
complex of flat modules concentrated in degrees `≥ a + 1`. -/
theorem isGE_derivedPullback_truncGE_of_iso {T : CommRingCat.{u}}
    (L : DerivedCategory (Spec T).Modules)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (a b : ℤ) [CochainComplex.IsStrictlyLE P b]
    [∀ i, Module.Free T (P.X i)]
    (hd : P.d a (a + 1) = 0)
    (e : L ≅ (tilde.functor T).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    {Y : Scheme.{u}} (g : Y ⟶ Spec T) :
    ((derivedPullback g.toLRSHom.toShHom).obj
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj L)).IsGE (a + 1) := by
  let F₀ := ((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hF₀d : F₀.d (a + 1 - 1) (a + 1) = 0 := by
    change (tilde.functor T).map (P.d (a + 1 - 1) (a + 1)) = 0
    rw [show a + 1 - 1 = a by omega, hd, Functor.map_zero]
  have : CochainComplex.IsStrictlyLE (CochainComplex.truncGE F₀ (a + 1)) (max b (a + 1)) :=
    (CochainComplex.isStrictlyLE_iff ..).2 fun i hi =>
      ((tilde.functor T).map_isZero (P.isZero_of_isStrictlyLE b i (by omega))).of_iso
        (CochainComplex.truncGEXIso F₀ (a + 1) i (by omega))
  have eL : (DerivedCategory.TStructure.t.truncGE (a + 1)).obj L ≅
      DerivedCategory.Q.obj (CochainComplex.truncGE F₀ (a + 1)) :=
    (DerivedCategory.TStructure.t.truncGE (a + 1)).mapIso
      (e ≪≫ ((tilde.functor T).mapDerivedCategoryFactors.app P)) ≪≫ truncGEQIso F₀ (a + 1)
  exact (AlgebraicGeometry.isGE_congr ((derivedPullback g.toLRSHom.toShHom).mapIso eL)
    (a + 1)).2 (isGE_derivedPullback_Q_obj_of_isFlat g _ (max b (a + 1)) (a + 1)
      (isFlat_truncGE_X F₀ (a + 1) (fun i => isFlat_tilde_of_flat (P.X i)) hF₀d))

/-! ### The pieces of the stratum -/

section Pieces

variable {E a} {r : ℕ}

/-- **A morphism universally of bottom rank `r` is covered by affine pieces of charts on which the
bottom differential vanishes.** Around a point `z` choose the chart at its image, whose bottom term
is free of rank `β_a = r`; the pullback of the dual cokernel sheaf is finite locally free of rank
`r`, hence free of rank `r` on a principal open of an affine neighbourhood, and there the
surjection of the free bottom term onto it is an isomorphism, so the base changed bottom
differential vanishes (`LinearMap.baseChange_eq_zero_of_dualCoker_equiv`). The bottom term of
the chart is free of rank `r`. -/
theorem exists_piece
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    {Z : Scheme.{u}} (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j) (z : Z) :
    ∃ (T : CommRingCat.{u}) (w : Spec T ⟶ Z) (_ : IsOpenImmersion w) (c : Chart E a)
      (ψ : c.R ⟶ T), z ∈ Set.range w.base ∧ w ≫ j = Spec.map ψ ≫ c.ι ∧
        (ModuleCat.extendScalars.{u, u, u} ψ.hom).map c.d = 0 ∧
          Nonempty (c.P.X a ≃ₗ[c.R] (Fin r → c.R)) := by
  set hPC := Scheme.Modules.isPseudoCoherent_of_isPerfect E hE
  set x := j.base z
  set c := chartAt hE b htor x
  have hr : DerivedFibreBetti.derivedFiberBetti X E hPC a x = r :=
    derivedFiberBetti_eq_of_isUniversallyFreeBottom E hPC a r hj z
  obtain ⟨eM⟩ := nonempty_chartAt_X_equiv hE b htor x a
  let eM' : c.P.X a ≃ₗ[c.R] (Fin r → c.R) :=
    eM.trans (LinearEquiv.funCongrLeft _ _ (finCongr hr).symm)
  obtain ⟨z', hz'⟩ : z ∈ Set.range (pullback.fst j c.ι).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact mem_range_chartAt hE b htor x
  have hsnd : IsUniversallyFreeBottom E a r (pullback.snd j c.ι ≫ c.ι) := by
    rw [← pullback.condition]
    exact hj.comp _
  have hQ := (c.isUniversallyFreeBottom_comp_iff (pullback.snd j c.ι) r).1 hsnd
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at hQ
  obtain ⟨V, hz'V⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top (pullback j c.ι)).ge (Set.mem_univ z'))
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨y, hy⟩ : z' ∈ Set.range V.2.fromSpec.base := by rwa [V.2.range_fromSpec]
  set φ := Spec.preimage (V.2.fromSpec ≫ pullback.snd j c.ι)
  have hring := (c.isFiniteLocallyFreeOfRank_pullback_dualCoker_iff φ r).1
    ((hQ.restrict V.2.fromSpec).of_iso ((Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
      c.pullbackDualCokerIso V.2.fromSpec (pullback.snd j c.ι)))
  let := φ.hom.toAlgebra
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨g, hg, ⟨eQ⟩⟩ := hring.exists_away_baseChange_equiv _ y.asIdeal
  let lg : Γ(pullback j c.ι, V.1) ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap _ _)
  have : IsOpenImmersion (Spec.map lg) := Scheme.isOpenImmersion_SpecMap_localizationAway g
  refine ⟨CommRingCat.of (Localization.Away g), Spec.map lg ≫ V.2.fromSpec ≫ pullback.fst j c.ι,
    inferInstance, c, φ ≫ lg, ?_, ?_, ?_, ⟨eM'⟩⟩
  · obtain ⟨t, ht⟩ : y ∈ Set.range (Spec.map lg).base := by
      have hb : y ∈ PrimeSpectrum.basicOpen g := hg
      rwa [← Scheme.Hom.opensRange_localizationAway g] at hb
    refine ⟨t, ?_⟩
    have ht' : (Spec.map lg) t = y := ht
    simp only [Scheme.Hom.comp_apply, ht', hy, hz']
  · rw [Spec.map_comp, Category.assoc, Category.assoc, pullback.condition, Spec.map_preimage,
      Category.assoc, Category.assoc]
  · have hinst : (φ ≫ lg).hom.toAlgebra =
        (inferInstance : Algebra c.R (Localization.Away g)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have h0 : (let := (φ ≫ lg).hom.toAlgebra
        c.d.hom.baseChange (Localization.Away g) = 0) := by
      rw [hinst]
      exact LinearMap.baseChange_eq_zero_of_dualCoker_equiv _ c.d.hom eM' eQ
    exact ModuleCat.hom_ext h0

/-- Derived pullback along a composite of morphisms of schemes, on an object. -/
def pullbackHomologyCompIsoAux {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing C.toSheafedSpace))) :
    (derivedPullback f.toLRSHom.toShHom).obj ((derivedPullback g.toLRSHom.toShHom).obj L) ≅
      (derivedPullback (f ≫ g).toLRSHom.toShHom).obj L :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _).app L ≪≫
    eqToIso (congrArg (fun k => (derivedPullback k).obj L) (comp_toLRSHom_toShHom f g).symm)

/-- Derived pullback along the two sides of a commutative square, on an object. -/
def derivedPullbackSquareObjIso {A B C D : Scheme.{u}} (f₁ : A ⟶ B) (g₁ : B ⟶ D) (f₂ : A ⟶ C)
    (g₂ : C ⟶ D) (h : f₁ ≫ g₁ = f₂ ≫ g₂)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.toSheafedSpace))) :
    (derivedPullback f₁.toLRSHom.toShHom).obj ((derivedPullback g₁.toLRSHom.toShHom).obj L) ≅
      (derivedPullback f₂.toLRSHom.toShHom).obj ((derivedPullback g₂.toLRSHom.toShHom).obj L) :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _).app L ≪≫
    eqToIso (congrArg (fun k => (derivedPullback k).obj L)
      (by rw [← comp_toLRSHom_toShHom, ← comp_toLRSHom_toShHom, h])) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _).app L).symm

/-- Derived pullback along equal morphisms of schemes, on an object. -/
def derivedPullbackEqObjIso {A B : Scheme.{u}} {f₁ f₂ : A ⟶ B} (h : f₁ = f₂)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing B.toSheafedSpace))) :
    (derivedPullback f₁.toLRSHom.toShHom).obj L ≅ (derivedPullback f₂.toLRSHom.toShHom).obj L :=
  eqToIso (by rw [h])

/-- On a piece `w : Spec T ⟶ Z` with `w ≫ j = Spec.map ψ ≫ ι`, the derived pullback of `Lj^* E`
is the sheafification of the base changed complex of the chart. -/
def derivedPullbackPieceIso {Z : Scheme.{u}} (j : Z ⟶ X) {T : CommRingCat.{u}} (w : Spec T ⟶ Z)
    (c : Chart E a) (ψ : c.R ⟶ T) (hwj : w ≫ j = Spec.map ψ ≫ c.ι) :
    (derivedPullback w.toLRSHom.toShHom).obj ((derivedPullback j.toLRSHom.toShHom).obj E) ≅
      (tilde.functor T).mapDerivedCategory.obj (DerivedCategory.Q.obj (c.baseChange ψ)) :=
  (pullbackHomologyCompIsoAux w j E) ≪≫ derivedPullbackEqObjIso hwj E ≪≫
    c.derivedPullbackIso ψ

/-- The base changed complex of a chart has free terms. -/
theorem Chart.free_baseChange (c : Chart E a) {T : CommRingCat.{u}} (ψ : c.R ⟶ T) (i : ℤ) :
    Module.Free T ((c.baseChange ψ).X i) :=
  let := ψ.hom.toAlgebra
  inferInstanceAs (Module.Free T (T ⊗[c.R] c.P.X i))

/-- The base changed complex of a chart is bounded above. -/
theorem Chart.isStrictlyLE_baseChange (c : Chart E a) {T : CommRingCat.{u}} (ψ : c.R ⟶ T) :
    CochainComplex.IsStrictlyLE (c.baseChange ψ) c.b :=
  (CochainComplex.isStrictlyLE_iff ..).2 fun i hi =>
    (ModuleCat.extendScalars.{u, u, u} ψ.hom).map_isZero (c.P.isZero_of_isStrictlyLE c.b i hi)

/-- If the base changed bottom differential of a chart vanishes, so does the differential out of
degree `a` of the base changed complex. -/
theorem Chart.baseChange_d_eq_zero (c : Chart E a) {T : CommRingCat.{u}} (ψ : c.R ⟶ T)
    (hd : (ModuleCat.extendScalars.{u, u, u} ψ.hom).map c.d = 0) :
    (c.baseChange ψ).d a (a + 1) = 0 := by
  rw [← (c.baseChange ψ).d_comp_XIsoOfEq_hom (show (ComplexShape.up ℤ).next a = a + 1 by simp)]
  change (ModuleCat.extendScalars.{u, u, u} ψ.hom).map c.d ≫ _ = 0
  rw [hd, zero_comp]

/-- **On a morphism universally of bottom rank `r`, every derived pullback of the truncation
above degree `a` stays above it.** Locally on the source the morphism lands in a chart piece on
which the bottom differential vanishes (`exists_piece`); there the truncation commutes with
restriction (`nonempty_derivedPullback_truncGE_iso`) and is a bounded complex of flat modules
concentrated in degrees `≥ a + 1` (`isGE_derivedPullback_truncGE_of_iso`). -/
theorem isGE_derivedPullback_truncGE
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    {Z : Scheme.{u}} (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j) {Y : Scheme.{u}}
    (g : Y ⟶ Z) :
    ((derivedPullback g.toLRSHom.toShHom).obj
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj
        ((derivedPullback j.toLRSHom.toShHom).obj E))).IsGE (a + 1) := by
  refine isGE_of_forall_exists_openImmersion _ _ fun y => ?_
  obtain ⟨T, w, hw, c, ψ, hz, hwj, hd, -⟩ := exists_piece hE b htor j hj (g.base y)
  refine ⟨pullback g w, pullback.fst g w, inferInstance, ?_, ?_⟩
  · rwa [IsOpenImmersion.range_pullbackFst]
  obtain ⟨e₂⟩ := nonempty_derivedPullback_truncGE_iso w
    ((derivedPullback j.toLRSHom.toShHom).obj E) (a + 1)
  have := c.free_baseChange ψ
  have := c.isStrictlyLE_baseChange ψ
  have hlocal := isGE_derivedPullback_truncGE_of_iso _ (c.baseChange ψ) a c.b
    (c.baseChange_d_eq_zero ψ hd) (derivedPullbackPieceIso j w c ψ hwj) (pullback.snd g w)
  exact (AlgebraicGeometry.isGE_congr
    (derivedPullbackSquareObjIso (pullback.fst g w) g (pullback.snd g w) w pullback.condition _ ≪≫
      (derivedPullback (pullback.snd g w).toLRSHom.toShHom).mapIso e₂) (a + 1)).2 hlocal

/-- **Part (3): base change for the bottom cohomology along a morphism universally of bottom
rank `r`.** If `j : Z ⟶ X` is universally of bottom rank `r` then, for every `g : Y ⟶ Z`,
`H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)`. -/
theorem nonempty_pullbackHomology_comp_iso_of_isUniversallyFreeBottom
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    {Z : Scheme.{u}} (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j) {Y : Scheme.{u}}
    (g : Y ⟶ Z) :
    Nonempty (pullbackHomology E a (g ≫ j) ≅
      (Scheme.Modules.pullback g).obj (pullbackHomology E a j)) :=
  nonempty_pullbackHomology_comp_iso E a j
    (isGE_derivedPullback_of_hasTorAmplitude E a b htor j) g
    (isGE_derivedPullback_truncGE hE b htor j hj g)

end Pieces

end AlgebraicGeometry.BottomRankStratum

end
