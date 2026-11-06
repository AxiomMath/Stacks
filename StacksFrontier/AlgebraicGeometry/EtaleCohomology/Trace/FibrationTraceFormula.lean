module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibrationBaseTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCoreProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The trace formula over a fibration into curves

This file carries out the geometric step of the proof of [Stacks, Tag 03V3]: the trace formula
for `D_ctf` on a scheme `U` separated of finite type over a finite field `k` follows from the
trace formula on the base of a morphism `g : U ⟶ A` whose fibres over the rational points have
dimension at most one, by proper base change, from the case of curves.

Let `j : U ⟶ X̄` be a compactification of `U` and `A ⟶ P` one of `A`. The graph of `g` gives an
immersion `U ⟶ X̄ ×_k P`; its scheme-theoretic image `X̄'` is a compactification of `U`, with
proper projections `X̄' ⟶ X̄` and `f̄ : X̄' ⟶ P`. Then:

* the trace formula on `X̄` follows from the one on `X̄'`
  (`Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_compactificationHom`);
* on `X̄'` it follows from the trace formula for `R f̄_* j'_! K` on `P` and on the fibres
  (`Stacks.EtaleCohomology.cohomologicalTraceFormula_of_isProper_of_rationalFibre`);
* `R f̄_* j'_! K` is extended by zero from `A`, where it is `R f'_*` of a complex in `D_ctf`
  (`Stacks.EtaleCohomology.cohomologicalTraceFormula_directImage_of_isPullback`), so the trace
  formula on `P` is the hypothesis on the base;
* on the fibre `X̄'_y` over a rational point `y` of `P` the complex is extended by zero from the
  fibre `U_y` of `g`, a curve, where the trace formula is
  `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf`.

That `R f'_*` preserves `D_ctf` for the proper `f'` is the proposition
`Stacks.EtaleCohomology.ProperDirectImageCtfInput`, the statement
`Stacks.EtaleCohomology.isCtf_etaleModuleDerivedDirectImage_of_isProper` (from the
constructibility of [Stacks, Tag 0GL0]); it is carried as one named hypothesis.

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main definitions

* `Stacks.EtaleCohomology.ProperDirectImageCtfInput`.

## Main results

* `Stacks.EtaleCohomology.isCtf_extensionByZero_of_isOpenImmersion`,
  `Stacks.EtaleCohomology.isCtf_inverseImage`: `D_ctf` along `j_!` and `f^{-1}`, on schemes.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_fibration`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **`R π_*` preserves `D_ctf` along proper morphisms**, for the coefficient ring `Λ`: the
statement of `Stacks.EtaleCohomology.isCtf_etaleModuleDerivedDirectImage_of_isProper` for
`Λ`, without its constructibility input. -/
def ProperDirectImageCtfInput (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] : Prop :=
  ∀ {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [IsNoetherian Y] (hX : B.Contains X)
    (hY : B.Contains Y) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)),
    IsCtf B (B.obj X hX) Λ (DerivedCategory.Plus.ι.obj K) →
      IsCtf B (B.obj Y hY) Λ (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K))

section Ctf

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ]

/-- **`j_!` preserves `D_ctf`** along an open immersion `j : U ⟶ X` of quasi-compact schemes with
`X` quasi-separated, on schemes of the big étale site. -/
theorem isCtf_extensionByZero_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (hU : B.Contains U) (hX : B.Contains X) (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (hC : IsCtf B (B.obj U hU) Λ (DerivedCategory.Q.obj C.obj)) :
    IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj C).obj) := by
  let Zc : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hic : Set.range j.base = (Set.range Zc.subschemeι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  have : IsFinite Zc.subschemeι := ((IsClosedImmersion.iff_isFinite_and_mono _).mp inferInstance).1
  have : LocallyOfFiniteType Zc.subschemeι :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp inferInstance).2
  have hZ : B.Contains Zc.subscheme :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact Zc.subschemeι).trans_lt hX
  have : IsOpenImmersion (B.inclusion.map
      (ObjectProperty.homMk j : B.obj U hU ⟶ B.obj X hX)) := inferInstanceAs (IsOpenImmersion j)
  have : IsClosedImmersion (B.inclusion.map
      (ObjectProperty.homMk Zc.subschemeι : B.obj Zc.subscheme hZ ⟶ B.obj X hX)) :=
    inferInstanceAs (IsClosedImmersion Zc.subschemeι)
  have : CompactSpace (B.obj X hX).obj := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (B.obj X hX).obj := inferInstanceAs (QuasiSeparatedSpace X)
  have : CompactSpace (B.obj U hU).obj := inferInstanceAs (CompactSpace U)
  exact IsCtf.extensionByZero B Λ (ObjectProperty.homMk j : B.obj U hU ⟶ B.obj X hX)
    (ObjectProperty.homMk Zc.subschemeι : B.obj Zc.subscheme hZ ⟶ B.obj X hX) hic hC

/-- **`f^{-1}` preserves `D_ctf`**, on schemes of the big étale site. -/
theorem isCtf_inverseImage {Y X : Scheme.{u}} (f : Y ⟶ X) (hY : B.Contains Y) (hX : B.Contains X)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hC : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj C.obj)) :
    IsCtf B (B.obj Y hY) Λ (DerivedCategory.Q.obj
      ((etaleModuleInverseImage.{u, 0} Λ f).mapCochainComplexPlus.obj C).obj) :=
  (IsCtf.pullback B Λ (ObjectProperty.homMk f : B.obj Y hY ⟶ B.obj X hX) hC).of_iso B _ Λ
    ((etaleModuleInverseImage.{u, 0} Λ f).mapDerivedCategoryFactors.app C.obj)

end Ctf

section Fibration

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  (B : BigEtaleSite.{u})

/-- **The trace formula over a fibration into curves.** Let `g : U ⟶ A` be a morphism of schemes
separated of finite type over `k`, lying in the big étale site, whose fibres over the rational
points of a compactification `A ⟶ P` have dimension at most one, and let `j : U ⟶ X̄` be a
compactification. If `R π_*` preserves `D_ctf` along proper morphisms and the trace formula holds
on `P` for every complex in `D_ctf(A, Λ)` extended by zero, then it holds on `X̄` for `j_! K`, for
every `K` in `D_ctf(U, Λ)`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_fibration (hΛ : (Nat.card Λ : k) ≠ 0)
    (hctf : ProperDirectImageCtfInput B Λ)
    {U A : Scheme.{u}} (fU : U ⟶ Spec (.of k)) [LocallyOfFiniteType fU] [IsSeparated fU]
    [QuasiCompact fU] (fA : A ⟶ Spec (.of k)) [LocallyOfFiniteType fA] [IsSeparated fA]
    [QuasiCompact fA] (J : CompactificationOf (Over.mk fU)) (JA : CompactificationOf (Over.mk fA))
    (g : U ⟶ A) (hg : g ≫ fA = fU)
    (hdim : ∀ y : Spec (.of k) ⟶ JA.space, y ≫ JA.toBase = 𝟙 _ →
      ∀ {Z : Scheme.{u}} (a : Z ⟶ U) (c : Z ⟶ Spec (.of k)),
        IsPullback a c (g ≫ JA.immersion) y → topologicalKrullDim Z ≤ 1)
    (hU : B.Contains U) (hA : B.Contains A) (hk : B.Contains (Spec (.of k)))
    (hIH : ∀ (KA : CochainComplex.Plus (EtaleModules.{u, 0} Λ A))
      (_ : IsCtf B (B.obj A hA) Λ (DerivedCategory.Q.obj KA.obj)) (hKAs : HasPerfectStalks Λ KA),
      CohomologicalTraceFormula Λ kbar p q hcard (Over.mk JA.toBase)
        ((etaleModuleExtensionByZero.{u, 0} Λ JA.immersion).mapCochainComplexPlus.obj KA)
        (hasPerfectStalks_extensionByZero Λ JA.immersion KA hKAs))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (hK : IsCtf B (B.obj U hU) Λ (DerivedCategory.Q.obj K.obj)) (hKs : HasPerfectStalks Λ K) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian fU
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace fU
  have : IsNoetherian U := { }
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian fA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace fA
  have : IsNoetherian A := { }
  -- the graph immersion `U ⟶ X̄ ×_k P` and its scheme-theoretic image `X̄'`
  let φ : U ⟶ pullback J.toBase JA.toBase := pullback.lift J.immersion (g ≫ JA.immersion) (by
    rw [J.immersion_toBase, Category.assoc, JA.immersion_toBase, hg])
  have : IsImmersion φ := by
    have : IsImmersion (φ ≫ pullback.fst J.toBase JA.toBase) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsImmersion.of_comp _ (pullback.fst J.toBase JA.toBase)
  let πl : φ.image ⟶ JA.space := φ.imageι ≫ pullback.snd J.toBase JA.toBase
  let Pa := pullback πl JA.immersion
  let jA : U ⟶ Pa := pullback.lift φ.toImage g (by
    rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_snd])
  have : IsOpenImmersion jA := by
    have : IsOpenImmersion (jA ≫ pullback.fst πl JA.immersion) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst πl JA.immersion)
  have hJ' : (jA ≫ pullback.fst πl JA.immersion) ≫
      (φ.imageι ≫ pullback.fst J.toBase JA.toBase ≫ J.toBase) = fU := by
    rw [Category.assoc, pullback.lift_fst_assoc, Scheme.Hom.toImage_imageι_assoc,
      pullback.lift_fst_assoc, J.immersion_toBase]
  let J' : CompactificationOf (Over.mk fU) :=
    ⟨StructuredArrow.mk (Y := Over.mk (φ.imageι ≫ pullback.fst J.toBase JA.toBase ≫ J.toBase))
      (Over.homMk (U := Over.mk fU) (jA ≫ pullback.fst πl JA.immersion) hJ'),
      ⟨inferInstanceAs (IsOpenImmersion (jA ≫ pullback.fst πl JA.immersion)),
        inferInstanceAs (IsProper (φ.imageι ≫ pullback.fst J.toBase JA.toBase ≫ J.toBase))⟩⟩
  have : IsOpenImmersion J'.immersion :=
    inferInstanceAs (IsOpenImmersion (jA ≫ pullback.fst πl JA.immersion))
  have : IsProper J'.toBase :=
    inferInstanceAs (IsProper (φ.imageι ≫ pullback.fst J.toBase JA.toBase ≫ J.toBase))
  let γ : J' ⟶ J := ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (φ.imageι ≫ pullback.fst J.toBase JA.toBase) (Category.assoc _ _ _)) (by
      ext
      show (jA ≫ pullback.fst πl JA.immersion) ≫ φ.imageι ≫ pullback.fst J.toBase JA.toBase =
        J.immersion
      rw [Category.assoc, pullback.lift_fst_assoc, Scheme.Hom.toImage_imageι_assoc,
        pullback.lift_fst]))
  refine cohomologicalTraceFormula_extensionByZero_of_compactificationHom Λ kbar p q hcard fU γ K
    hKs ?_
  -- the projection `f̄ : X̄' ⟶ P`, over `k`
  have hπ : πl ≫ JA.toBase = φ.imageι ≫ pullback.fst J.toBase JA.toBase ≫ J.toBase := by
    rw [Category.assoc, ← pullback.condition]
  let π : Over.mk J'.toBase ⟶ Over.mk JA.toBase := Over.homMk (V := Over.mk JA.toBase) πl hπ
  have : IsProper π.left := inferInstanceAs (IsProper πl)
  -- the complexes `L = (j'_A)_! K` on `X̄'_A` and `C = b_! L` on `X̄'`
  let L := (etaleModuleExtensionByZero.{u, 0} Λ jA).mapCochainComplexPlus.obj K
  let C := (etaleModuleExtensionByZero.{u, 0} Λ
    (pullback.fst πl JA.immersion)).mapCochainComplexPlus.obj L
  have hCs : HasPerfectStalks Λ C :=
    hasPerfectStalks_extensionByZero Λ _ L (hasPerfectStalks_extensionByZero Λ jA K hKs)
  let eC : C ≅ (etaleModuleExtensionByZero.{u, 0} Λ J'.immersion).mapCochainComplexPlus.obj K :=
    ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jA (pullback.fst πl JA.immersion)).symm _).app
        K.obj)
  refine cohomologicalTraceFormula_of_iso Λ kbar p q hcard eC hCs _ ?_
  have := etaleModules_enoughInjectives.{u, 0} Λ φ.image
  have := etaleModules_enoughInjectives.{u, 0} Λ Pa
  obtain ⟨T, ψ, hψ, hT, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution (𝟭 _) C (𝟙 _)
  obtain ⟨TA, ψA, hψA, hTA, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution (𝟭 _) L (𝟙 _)
  -- the base: `R f'_* L` lies in `D_ctf(A, Λ)`
  have : CompactSpace φ.image := QuasiCompact.compactSpace_of_compactSpace J'.toBase
  have : CompactSpace Pa :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst πl JA.immersion ≫ J'.toBase)
  have : QuasiSeparatedSpace φ.image := quasiSeparatedSpace_of_quasiSeparated J'.toBase
  have : IsLocallyNoetherian Pa :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst πl JA.immersion ≫ J'.toBase)
  have : IsNoetherian Pa := { }
  have : IsNoetherian (Over.mk fA).left := inferInstanceAs (IsNoetherian A)
  have : QuasiCompact (Over.mk JA.toBase).hom := inferInstanceAs (QuasiCompact JA.toBase)
  have : LocallyOfFiniteType (Over.mk JA.toBase).hom :=
    inferInstanceAs (LocallyOfFiniteType JA.toBase)
  have hPa : B.Contains Pa :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
      (pullback.fst πl JA.immersion ≫ J'.toBase)).trans_lt hk
  have hL : IsCtf B (B.obj Pa hPa) Λ (DerivedCategory.Q.obj L.obj) :=
    isCtf_extensionByZero_of_isOpenImmersion B Λ jA hU hPa K hK
  have := etaleModules_enoughInjectives.{u, 0} Λ A
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd πl JA.immersion)) TA
    (fun n => have := hTA n; Functor.rightAcyclic_of_injective _ _)
  have := isIso_plusQ_map_of_quasiIso Λ ψA hψA
  have hKA : IsCtf B (B.obj A hA) Λ (DerivedCategory.Q.obj
      ((etaleModuleDirectImage.{u, 0} Λ (pullback.snd πl JA.immersion)).mapCochainComplexPlus.obj
        TA).obj) :=
    (hctf (pullback.snd πl JA.immersion) hPa hA (DerivedCategory.Plus.Q.obj L) hL).of_iso B _ Λ
      (DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
        (pullback.snd πl JA.immersion)).mapIso (asIso (DerivedCategory.Plus.Q.map ψA)) ≪≫
        (asIso ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd πl JA.immersion)).mapCochainComplexPlusDerivedUnit.app TA)).symm))
  have hKAs := hasPerfectStalks_of_isCtf B hA Λ _ hKA
  obtain ⟨hD, hbase⟩ := cohomologicalTraceFormula_directImage_of_isPullback Λ kbar p q hcard
    (Y := Over.mk JA.toBase) πl JA.immersion (pullback.fst πl JA.immersion)
    (pullback.snd πl JA.immersion) (IsPullback.of_hasPullback πl JA.immersion) L T ψ hψ hT TA ψA
    hψA hTA hKAs (hIH _ hKA hKAs)
  -- the fibration
  refine cohomologicalTraceFormula_of_isProper_of_rationalFibre Λ kbar p q hcard π C hCs T ψ hψ hT
    hD hbase ?_
  intro y
  -- the fibre `X̄'_y` and the fibre `U_y = U ×_{X̄'} X̄'_y` of `g`, a curve
  let fy := pullback.fst π.left y.1
  have : QuasiCompact J'.immersion :=
    inferInstanceAs (QuasiCompact (jA ≫ pullback.fst πl JA.immersion))
  let hUm := pullback.fst J'.immersion fy
  let pY := pullback.snd J'.immersion fy
  let fyk := pY ≫ pullback.snd π.left y.1
  let Jy : CompactificationOf (Over.mk fyk) :=
    ⟨StructuredArrow.mk (Y := Over.mk (pullback.snd π.left y.1))
      (Over.homMk (U := Over.mk fyk) pY rfl),
      ⟨inferInstanceAs (IsOpenImmersion pY),
        inferInstanceAs (IsProper (pullback.snd π.left y.1))⟩⟩
  have h₁ := IsPullback.of_hasPullback J'.immersion fy
  have heq : J'.immersion ≫ π.left = g ≫ JA.immersion := by
    show (jA ≫ pullback.fst πl JA.immersion) ≫ πl = g ≫ JA.immersion
    rw [Category.assoc, pullback.condition, pullback.lift_snd_assoc]
  have hpb : IsPullback hUm fyk (g ≫ JA.immersion) y.1 :=
    heq ▸ h₁.paste_vert (IsPullback.of_hasPullback π.left y.1)
  have : IsProper (pullback.snd π.left y.1) := inferInstance
  have : LocallyOfFiniteType (pullback.snd π.left y.1) :=
    ‹IsProper (pullback.snd π.left y.1)›.toLocallyOfFiniteType
  have : IsOpenImmersion pY := inferInstanceAs (IsOpenImmersion (pullback.snd J'.immersion fy))
  have : LocallyOfFiniteType pY := inferInstance
  have : LocallyOfFiniteType fyk :=
    MorphismProperty.comp_mem @LocallyOfFiniteType _ _ ‹_› ‹_›
  have hUy : B.Contains (pullback J'.immersion fy) :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact fyk).trans_lt hk
  let Ky := (etaleModuleInverseImage.{u, 0} Λ hUm).mapCochainComplexPlus.obj K
  have hKys : HasPerfectStalks Λ Ky := isPerfect_stalk_inverseImage Λ hUm K hKs
  have hcurve := cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf Λ kbar p q
    hcard (hΛ := hΛ) (curveTraceCore Λ k hΛ kbar p q hcard) B fyk
    (hdim y.1 y.2 hUm fyk hpb) Jy Ky hUy (isCtf_inverseImage B Λ hUm hUy hU K hK) hKys
  let e₂ : (etaleModuleInverseImage.{u, 0} Λ fy).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ J'.immersion).mapCochainComplexPlus.obj K) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ pY).mapCochainComplexPlus.obj Ky :=
    ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ h₁) _).app K.obj).symm
  exact cohomologicalTraceFormula_of_iso Λ kbar p q hcard
    (((etaleModuleInverseImage.{u, 0} Λ fy).mapCochainComplexPlus.mapIso eC) ≪≫ e₂).symm _ _
    hcurve

end Fibration

end Stacks.EtaleCohomology

end
