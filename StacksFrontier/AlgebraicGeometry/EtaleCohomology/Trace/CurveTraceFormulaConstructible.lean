module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaReduced
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfDenseOpen

/-!
# The trace formula for a constructible flat sheaf on a curve, from the core

Let `X` be a separated scheme of finite type and dimension at most one over a finite field `k`,
lying in a big étale site `B`, and `F` a constructible flat sheaf of `Λ`-modules on Mathlib's small
étale site of `X` (`Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule`) with perfect stalks.
Then `Stacks.EtaleCohomology.CurveTraceCore` gives the trace formula of [Stacks, Tag 03UG] for
`F`. On a reduced `X`, `F` is locally constant with finite projective values on a dense open
(`AlgebraicGeometry.exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant`, read back on
Mathlib's site), and the reduced case applies.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `exists_dense_isFiniteProjectiveLocallyConstant_of_isConstructibleFlat`
* `cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isConstructibleFlat`
* `cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_constructibleFlat_complex`
* `cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_locallyConstant`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- Local constancy with finite projective values of a restriction only depends on the étale
morphism, not on its spelling. -/
theorem isFiniteProjectiveLocallyConstant_etaleModuleRestriction_of_eq {Λ : Type r} [Ring Λ]
    {U X : Scheme.{u}} {g g' : U ⟶ X} [Etale g] [Etale g'] (h : g = g')
    (F : EtaleModules.{u, r} Λ X)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology
      ((etaleModuleRestriction.{u, r} Λ g).obj F)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology
      ((etaleModuleRestriction.{u, r} Λ g').obj F) := by
  subst h
  exact hF

/-- Local constancy with finite projective values of the inverse image along an open immersion `e`
gives it for the restriction to the open range of `e`. -/
private theorem isFiniteProjectiveLocallyConstant_restriction_opensRange {Λ : Type r} [Ring Λ]
    {U X : Scheme.{u}} (e : U ⟶ X) [IsOpenImmersion e] (F : EtaleModules.{u, r} Λ X)
    (he : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology
      ((etaleModuleInverseImage.{u, r} Λ e).obj F)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      e.opensRange.toScheme.smallEtaleTopology
      ((etaleModuleRestriction.{u, r} Λ e.opensRange.ι).obj F) := by
  let φ := IsOpenImmersion.isoOfRangeEq e.opensRange.ι e (by rw [Scheme.Opens.range_ι]; rfl)
  have h₁ := isFiniteProjectiveLocallyConstant_etaleModuleRestriction Λ φ.hom _
    (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      ((etaleModuleInverseImageRestrictionIso.{u, r} Λ e).app F) he)
  exact isFiniteProjectiveLocallyConstant_etaleModuleRestriction_of_eq
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) F
    (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      ((etaleModuleRestrictionCompIso.{u, r} Λ φ.hom e).app F) h₁)

/-- **A constructible flat sheaf on a reduced Noetherian scheme is locally constant with finite
projective values on a dense open**, on Mathlib's small étale site. -/
theorem exists_dense_isFiniteProjectiveLocallyConstant_of_isConstructibleFlat
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsReduced X.obj] [TopologicalSpace.NoetherianSpace X.obj]
    (Λ : Type r) [Ring Λ] (F : EtaleModules.{u, r} Λ X.obj)
    (hF : IsConstructibleFlatEtaleModule B X Λ F) :
    ∃ O : X.obj.Opens, Dense (O : Set X.obj) ∧
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ O.toScheme.smallEtaleTopology
        ((etaleModuleRestriction.{u, r} Λ O.ι).obj F) := by
  obtain ⟨O, o, ho, hd, hloc⟩ :=
    exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant B Λ X (ι := Unit)
      (fun _ => (etaleModulesToSmallEtale B X Λ).obj F) (fun _ => hF)
  let e := B.inclusion.map o
  have he : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ O.obj.smallEtaleTopology
      ((etaleModuleInverseImage.{u, r} Λ e).obj F) :=
    (SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B O Λ _).1
      (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
        (etaleModulesToSmallEtalePullbackIso B Λ o F).symm (hloc ()))
  exact ⟨e.opensRange, hd, isFiniteProjectiveLocallyConstant_restriction_opensRange e F he⟩

/-- **A bounded complex of constructible flat sheaves on a reduced Noetherian scheme has all its
terms locally constant with finite projective values on one dense open**, on Mathlib's small étale
site. -/
theorem exists_dense_isFiniteProjectiveLocallyConstant_of_complex
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsReduced X.obj] [TopologicalSpace.NoetherianSpace X.obj]
    (Λ : Type r) [Ring Λ] (C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ) (a b : ℤ)
    (ha : C.IsStrictlyGE a) (hb : C.IsStrictlyLE b)
    (hC : ∀ i, IsConstructibleFlatEtaleModule B X Λ (C.X i)) :
    ∃ O : X.obj.Opens, Dense (O : Set X.obj) ∧ ∀ i,
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ O.toScheme.smallEtaleTopology
        ((etaleModuleRestriction.{u, r} Λ O.ι).obj (C.X i)) := by
  obtain ⟨O, o, ho, hd, hloc⟩ :=
    exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_complex B Λ X C a b ha hb hC
  let e := B.inclusion.map o
  exact ⟨e.opensRange, hd, fun i =>
    isFiniteProjectiveLocallyConstant_restriction_opensRange e (C.X i)
      ((SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B O Λ _).1 (hloc i))⟩

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula passes along a surjective closed immersion.** For a compactification
`j : X ⟶ X̄`, a surjective closed immersion `i : X' ⟶ X` and a complex `K` with perfect stalks,
the trace formula for `j_! K` on `X̄` follows from the one for `t_! i^{-1} K` on the closure `Z̄`
of `X'` in `X̄`, `t : X' ⟶ Z̄` being the induced compactification: `K ≅ i_* i^{-1} K` and
`j_! i_* ≅ ι_* t_!` for the closed immersion `ι : Z̄ ⟶ X̄`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_surjective_isClosedImmersion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] (J : CompactificationOf (Over.mk f))
    {X' : Scheme.{u}} (i : X' ⟶ X) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hK : HasPerfectStalks Λ K)
    (hK' : HasPerfectStalks Λ
      ((etaleModuleExtensionByZero.{u, 0} Λ
        (J.restrictClosed i).immersion).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)))
    (h : CohomologicalTraceFormula Λ kbar p q hcard (Over.mk (J.restrictClosed i).toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ
          (J.restrictClosed i).immersion).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)) hK') :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hK) := by
  -- `K ≅ i_* i^{-1} K`: the open complement of `i` is empty
  let O : X.Opens := ⊥
  have hO : Set.range O.ι = (Set.range i)ᶜ := by
    rw [Scheme.Opens.range_ι, Set.range_eq_univ.2 hi, Set.compl_univ]
    rfl
  have : IsEmpty O.toScheme := ⟨fun x => x.2⟩
  have hu (n : ℤ) : IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app (K.obj.X n)) :=
    isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ i O.ι hO _
      (isZero_etaleModule_of_forall_isZero_sections Λ _ fun W =>
        isZero_etaleModule_sections_of_isEmpty Λ _ _
          ⟨fun w => (W.hom.base w : O.toScheme).2⟩)
  let e₁ : K ≅ (etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K) :=
    ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
      (fun n => @asIso _ _ _ _ ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app (K.obj.X n))
        (hu n))
      (fun _ _ _ => ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.naturality _).symm))
  -- `j_! i_* ≅ ι_* t_!`
  let N := etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i (J.closedImmersion i).toImage
    J.immersion (J.closedSpaceι i) (J.isPullback_restrictClosed i)
  let G := (etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K
  let e₂ : (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj G) ≅
      (etaleModuleDirectImage.{u, 0} Λ (J.closedSpaceι i)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ
            (J.restrictClosed i).immersion).mapCochainComplexPlus.obj
          G) :=
    ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
      (fun n => N.app (G.obj.X n)) (fun _ _ _ => (N.hom.naturality _).symm))
  let E := (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.mapIso e₁ ≪≫ e₂
  let ιO : Over.mk (J.restrictClosed i).toBase ⟶ Over.mk J.toBase :=
    Over.homMk (J.closedSpaceι i) rfl
  have : IsClosedImmersion ιO.left := inferInstanceAs (IsClosedImmersion (J.closedSpaceι i))
  have hD := hasPerfectStalks_extensionByZero Λ J.immersion K hK
  have hE : HasPerfectStalks Λ ((etaleModuleDirectImage.{u, 0} Λ ιO.left).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ
          (J.restrictClosed i).immersion).mapCochainComplexPlus.obj
        G)) :=
    hasPerfectStalks_of_iso Λ (fun n => (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      ((ObjectProperty.ι _).mapIso E)) (fun a b => (E.hom.hom.comm a b).symm) hD
  exact cohomologicalTraceFormula_of_iso Λ kbar p q hcard E.symm hE hD
    (cohomologicalTraceFormula_directImage Λ kbar p q hcard ιO _ hK' hE h)

/-- A scheme with a surjective closed immersion into `X` has dimension at most that of `X`. -/
private theorem topologicalKrullDim_le_one_of_surjective_isClosedImmersion {X X' : Scheme.{u}}
    (i : X' ⟶ X) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (hdim : topologicalKrullDim X ≤ 1) : topologicalKrullDim X' ≤ 1 :=
  (IsHomeomorph.topologicalKrullDim_eq i.base
    (isHomeomorph_iff_isEmbedding_surjective.2 ⟨i.isClosedEmbedding.isEmbedding, hi⟩)).trans_le hdim

/-- **The trace formula for a single sheaf passes along a surjective closed immersion.** It
suffices to prove it for the inverse image `i^{-1} F` and the compactification `J.restrictClosed i`
of the source. -/
private theorem cohomologicalTraceFormula_single_of_surjective_isClosedImmersion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] (J : CompactificationOf (Over.mk f))
    {X' : Scheme.{u}} (i : X' ⟶ X) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (F : EtaleModules.{u, 0} Λ X)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
    (h : ∀ hFs' : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ i).obj F),
        CochainComplex.plus_singleFunctor_obj _⟩,
      CohomologicalTraceFormula Λ kbar p q hcard (Over.mk (J.restrictClosed i).toBase)
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (J.restrictClosed i).immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ i).obj F),
          CochainComplex.plus_singleFunctor_obj _⟩)
        (hasPerfectStalks_extensionByZero Λ (J.restrictClosed i).immersion _ hFs')) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) := by
  let K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X) :=
    ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩
  let eS := (singlePlusFunctorCompMapCochainComplexPlusIso
    (etaleModuleInverseImage.{u, 0} Λ i)).app F
  have hFs' := hasPerfectStalks_of_iso Λ
    (fun n => (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      ((ObjectProperty.ι _).mapIso eS)) (fun a b => (eS.hom.hom.comm a b).symm)
      (isPerfect_stalk_inverseImage Λ i K hFs)
  have hK' := hasPerfectStalks_extensionByZero Λ (J.restrictClosed i).immersion _
    (isPerfect_stalk_inverseImage Λ i K hFs)
  exact cohomologicalTraceFormula_extensionByZero_of_surjective_isClosedImmersion Λ kbar p q hcard
    f J i hi K hFs hK' <| cohomologicalTraceFormula_of_iso Λ kbar p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ
        (J.restrictClosed i).immersion).mapCochainComplexPlus.mapIso
      eS.symm) _ _ (h hFs')

variable [Finite Λ]

/-- **The trace formula `T''(X̄, j_! F) = T'(X̄, j_! F)` for a constructible flat sheaf on a curve,
from the core.** Let `X` be a separated scheme of finite type and dimension at most one over `k`,
lying in the big étale site `B`, with a compactification `j : X ⟶ X̄`, and `F` a constructible flat
sheaf of `Λ`-modules on Mathlib's small étale site of `X` with perfect stalks. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isConstructibleFlat
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) (B : BigEtaleSite.{u}) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hdim : topologicalKrullDim X.obj ≤ 1) (J : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsConstructibleFlatEtaleModule B X Λ F)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) := by
  let TC : TopologicalSpace.Closeds X.obj := ⊤
  let i := (Scheme.IdealSheafData.vanishingIdeal TC).subschemeι
  let X' := (Scheme.IdealSheafData.vanishingIdeal TC).subscheme
  have hi : Function.Surjective i.base :=
    Set.range_eq_univ.1 (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal TC)
  let XB : B.Scheme := B.obj X' (Scheme.size_lt_of_isClosedImmersion i X.property)
  let iB : XB ⟶ X := ObjectProperty.homMk i
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (i ≫ f)
  have : IsNoetherian X' := { }
  obtain ⟨O, hOd, hOl⟩ :=
    exists_dense_isFiniteProjectiveLocallyConstant_of_isConstructibleFlat B XB Λ
      ((etaleModuleInverseImage.{u, 0} Λ i).obj F)
      (IsConstructibleFlatEtaleModule.pullback B Λ iB hF)
  have hdim' := topologicalKrullDim_le_one_of_surjective_isClosedImmersion i hi hdim
  exact cohomologicalTraceFormula_single_of_surjective_isClosedImmersion Λ kbar p q hcard f J i hi
    F hFs fun hFs' => cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense Λ kbar
      p q hcard hcore (i ≫ f) hdim' (J.restrictClosed i) _ hFs' O hOd hOl

/-- **The trace formula `T''(X̄, j_! K) = T'(X̄, j_! K)` for a bounded complex of constructible
flat sheaves on a curve, from the core.** Let `X` be a separated scheme of finite type and
dimension at most one over `k`, lying in the big étale site `B`, with a compactification
`j : X ⟶ X̄`, and `K` a bounded below complex with perfect stalks, concentrated in degrees
`[a, a + N]`, all of whose terms are constructible flat sheaves of `Λ`-modules. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_constructibleFlat_complex
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) (B : BigEtaleSite.{u}) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hdim : topologicalKrullDim X.obj ≤ 1) (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)) (hKs : HasPerfectStalks Λ K) (a : ℤ)
    (N : ℕ) (hlo : ∀ n, n < a → IsZero (K.obj.X n)) (hhi : ∀ n, a + N < n → IsZero (K.obj.X n))
    (hK : ∀ n, IsConstructibleFlatEtaleModule B X Λ (K.obj.X n)) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  let TC : TopologicalSpace.Closeds X.obj := ⊤
  let i := (Scheme.IdealSheafData.vanishingIdeal TC).subschemeι
  let X' := (Scheme.IdealSheafData.vanishingIdeal TC).subscheme
  have hi : Function.Surjective i.base :=
    Set.range_eq_univ.1 (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal TC)
  let XB : B.Scheme := B.obj X' (Scheme.size_lt_of_isClosedImmersion i X.property)
  let iB : XB ⟶ X := ObjectProperty.homMk i
  let K' := (etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (i ≫ f)
  have : IsNoetherian X' := { }
  have hlo' : ∀ n, n < a → IsZero (K'.obj.X n) := fun n hn =>
    Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ i) (hlo n hn)
  have hhi' : ∀ n, a + N < n → IsZero (K'.obj.X n) := fun n hn =>
    Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ i) (hhi n hn)
  obtain ⟨O, hOd, hOl⟩ := exists_dense_isFiniteProjectiveLocallyConstant_of_complex B XB Λ K'.obj
    a (a + N) ((CochainComplex.isStrictlyGE_iff _ _).2 hlo')
    ((CochainComplex.isStrictlyLE_iff _ _).2 hhi') fun n =>
      IsConstructibleFlatEtaleModule.pullback B Λ iB (hK n)
  have hdim' := topologicalKrullDim_le_one_of_surjective_isClosedImmersion i hi hdim
  exact cohomologicalTraceFormula_extensionByZero_of_surjective_isClosedImmersion Λ kbar p q hcard
    f J i hi K hKs _
    (cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense_of_bounded Λ kbar p q
      hcard hcore (i ≫ f) hdim' (J.restrictClosed i) K' (isPerfect_stalk_inverseImage Λ i K hKs)
      a N hlo' hhi' O hOd fun n _ _ => hOl n)

/-- **The trace formula `T''(X̄, j_! F) = T'(X̄, j_! F)` for a locally constant sheaf with finite
projective values on a curve, from the core.** Let `X` be a separated scheme of finite type and
dimension at most one over `k` (not necessarily reduced), with a compactification `j : X ⟶ X̄`,
and `F` a sheaf of `Λ`-modules on `X_étale` with perfect stalks which is locally constant with
finite projective values. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_locallyConstant
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hdim : topologicalKrullDim X ≤ 1) (J : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) := by
  let TC : TopologicalSpace.Closeds X := ⊤
  let i := (Scheme.IdealSheafData.vanishingIdeal TC).subschemeι
  let X' := (Scheme.IdealSheafData.vanishingIdeal TC).subscheme
  have hi : Function.Surjective i.base :=
    Set.range_eq_univ.1 (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal TC)
  have hdim' := topologicalKrullDim_le_one_of_surjective_isClosedImmersion i hi hdim
  exact cohomologicalTraceFormula_single_of_surjective_isClosedImmersion Λ kbar p q hcard f J i hi
    F hFs fun hFs' => cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense Λ kbar
      p q hcard hcore (i ≫ f) hdim' (J.restrictClosed i) _ hFs' ⊤
      (by rw [TopologicalSpace.Opens.coe_top]; exact dense_univ)
      (isFiniteProjectiveLocallyConstant_etaleModuleRestriction Λ (⊤ : X'.Opens).ι _
        (isFiniteProjectiveLocallyConstant_etaleModuleInverseImage Λ i F hF))

end Standard

end Stacks.EtaleCohomology

end
