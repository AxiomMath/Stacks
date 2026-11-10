module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaFibrePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibrationTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GraphCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupport
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MvPolynomialChart

/-!
# The fibration step of the trace formula in any dimension

Let `U` be a separated scheme of finite type over a finite field `k` with a morphism
`g : U ⟶ 𝔸^n_k` over `k` all of whose fibres have dimension at most one. If the trace formula
holds up to dimension `n` and for curves, it holds for `U`. This is the fibration step of the
dévissage proving the trace formula in any dimension, [Stacks, Tag 03UI] (1).

The proof follows the source's "dévissage lemma (which uses proper base change etc.)". The trace
formula does not depend on the compactification
(`Stacks.EtaleCohomology.canonicalTraceFormula_iff_of_compactifications`), so it may be computed
through the closure `W` of `U` in `Ū ×_k ℙ^n_k`, which carries a proper `ḡ : W ⟶ ℙ^n_k`
extending `g`. With `J` a resolution of `j'_! K` by injectives, proper base change identifies
`RΓ_c(U_k̄, K)` with `RΓ(ℙ^n_k̄, ḡ_* J)` compatibly with Frobenius, and the stalk of `ḡ_* J` at a
rational point `y` with `RΓ_c` of the fibre `U_y`, a curve. The trace formula on `ℙ^n_k` (which has
dimension `n`) for `ḡ_* J`, which lies in `D_ctf` (`DirectImagePreservesCtf`), and on each `U_y`
then give the formula on `U`, the rational points of `U` being the disjoint union of those of the
`U_y`.

## Main definitions

* `Stacks.EtaleCohomology.DirectImagePreservesCtf`: the statement that `Rḡ_*` of the extension by
  zero of an object of `D_ctf` from an open on which `ḡ` has fibres of dimension at most one lies
  in `D_ctf`.

## Main results

* `Stacks.EtaleCohomology.fibredTraceFormula`.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize etaleModules_ab5OfSize

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]

/-- **Proper direct images of extensions by zero of `D_ctf` from curve fibrations lie in
`D_ctf`.** For proper `h : X ⟶ Y` over `k` (in the big étale site), an open immersion
`j_U : U ⟶ X` such that `j_U ≫ h` has fibres of dimension at most one, `K₀ ∈ D_ctf(U, Λ)` and a
resolution `J` of `j_{U!} K₀` by injectives, `h_* J ∈ D_ctf(Y, Λ)`. -/
def DirectImagePreservesCtf : Prop :=
  ∀ (X Y U : B.Scheme) (fY : Y.obj ⟶ Spec (.of k)) [IsProper fY] (h : X.obj ⟶ Y.obj) [IsProper h]
    [IsProper (h ≫ fY)] (jU : U.obj ⟶ X.obj) [IsOpenImmersion jU],
    (∀ y, topologicalKrullDim ((jU ≫ h).fiber y) ≤ 1) →
    ∀ (K₀ : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj)),
      IsCtf B U Λ (DerivedCategory.Q.obj K₀.obj) →
    ∀ (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
      (ψ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K₀ ⟶ J),
      QuasiIso ψ.hom → (∀ n, Injective (J.obj.X n)) →
      IsCtf B Y Λ (DerivedCategory.Q.obj
        ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj J).obj)

variable {B Λ k} (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- The structure morphism of the fibre `U_y` of `j' ≫ ḡ` over a rational point `y` factors
through `U`. -/
theorem fibreStructure_eq_pullback_fst_comp {U W P : Scheme.{u}} (j' : U ⟶ W) (gb : W ⟶ P)
    {πP : P ⟶ Spec (.of k)} {fU : U ⟶ Spec (.of k)} (hfU : j' ≫ gb ≫ πP = fU)
    {y : Spec (.of k) ⟶ P} (hy : y ≫ πP = 𝟙 _) :
    fibreStructure j' gb y = pullback.fst j' (pullback.fst gb y) ≫ fU := by
  rw [← hfU, pullback.condition_assoc, pullback.condition_assoc, hy, Category.comp_id]

/-- **The trace formula on a fibre.** If the trace formula holds for curves, it holds on the fibre
`U_y` of `j' ≫ ḡ` over a rational point `y`, when `j' ≫ ḡ` factors as `g ≫ ι` with `ι` injective
on points and all fibres of `g` of dimension at most one. -/
theorem exists_canonicalTraceFormula_fibre (h₁ : TraceFormulaUpToDim B Λ kbar p q hcard 1)
    (U : B.Scheme) {W P S : Scheme.{u}} (j' : U.obj ⟶ W) [IsOpenImmersion j'] (gb : W ⟶ P)
    [IsProper gb] (πP : P ⟶ Spec (.of k)) {fU : U.obj ⟶ Spec (.of k)} [QuasiCompact fU]
    [LocallyOfFiniteType fU] [IsSeparated fU] (hfU : j' ≫ gb ≫ πP = fU) (g : U.obj ⟶ S)
    (ι : S ⟶ P) (hι : Function.Injective ι.base) (hj'g : j' ≫ gb = g ≫ ι)
    (hfib : ∀ z, topologicalKrullDim (g.fiber z) ≤ 1) (y : Spec (.of k) ⟶ P)
    (hy : y ≫ πP = 𝟙 _) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj))
    (hK : IsCtf B U Λ (DerivedCategory.Q.obj K.obj)) :
    B.Contains (fibreScheme j' gb y) ∧
      CanonicalTraceFormula Λ kbar p q hcard (fibreStructure j' gb y)
        (fibreCompactification j' gb y)
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst j' (pullback.fst gb y))).mapCochainComplexPlus.obj K) := by
  have : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id πP y hy
  have hUy : B.Contains (fibreScheme j' gb y) :=
    Scheme.size_lt_of_isClosedImmersion (pullback.fst j' (pullback.fst gb y)) U.property
  have : LocallyOfFiniteType (pullback.fst j' (pullback.fst gb y)) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType
      (pullback.fst j' (pullback.fst gb y))).mp inferInstance).2
  obtain ⟨_, _, _⟩ : QuasiCompact (fibreStructure j' gb y) ∧
      LocallyOfFiniteType (fibreStructure j' gb y) ∧ IsSeparated (fibreStructure j' gb y) := by
    rw [fibreStructure_eq_pullback_fst_comp j' gb hfU hy]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨hUy, h₁ ⟨fibreScheme j' gb y, hUy⟩ (fibreStructure j' gb y)
    (topologicalKrullDim_fibreScheme_le_one j' gb πP y hy g ι hι hj'g hfib)
    (fibreCompactification j' gb y) _ (isCtf_inverseImage B Λ _ hUy _ _ hK)⟩

/-- **The stalk trace of `ḡ_* J` at a rational point is the sum over the fibre.** For a resolution
`J` of `j'_! K` by injectives and a rational point `y` of `P` at which the trace formula holds on
the fibre `U_y`, the trace of Frobenius on the stalk of `ḡ_* J` at `y` is the sum of the stalk
traces of `K` over the rational points of `U` lying over `y`. -/
theorem stalkTrace_directImage_eq_sum_fibre {U : Scheme.{u}} {W P : Over (Spec (.of k))}
    (j' : U ⟶ W.left) [IsOpenImmersion j'] (gb : W ⟶ P) [IsProper gb.left]
    {fU : U ⟶ Spec (.of k)} [QuasiCompact fU] (hfU : j' ≫ gb.left ≫ P.hom = fU)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.left))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj K ⟶ J)
    [QuasiIso ψ.hom] (hJ : ∀ n, Injective (J.obj.X n)) (y : Spec (.of k) ⟶ P.left)
    (hy : y ≫ P.hom = 𝟙 _)
    (hstalk : ∀ s : GeometricPoint (Spec (.of k)), StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (geometricStalkComplex.{u, 0} Λ s
        ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J)).obj)))
    (hUy : CanonicalTraceFormula Λ kbar p q hcard (fibreStructure j' gb.left y)
      (fibreCompactification j' gb.left y)
      ((etaleModuleInverseImage.{u, 0} Λ
        (pullback.fst j' (pullback.fst gb.left y))).mapCochainComplexPlus.obj K))
    (hsK : ∀ x : rationalPoints fU, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K)))
    (hs : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0}
      Λ kbar y ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J))))
    [Fintype {x : rationalPoints fU // x.1 ≫ j' ≫ gb.left = y}] :
    perfectDerivedTrace Λ ⟨_, hs⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ
        kbar p q hcard y ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J))) =
      ∑ x : {x : rationalPoints fU // x.1 ≫ j' ≫ gb.left = y}, perfectDerivedTrace Λ ⟨_, hsK x.1⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1.1 K)) := by
  obtain ⟨hXy, _, heqy⟩ := hUy
  have : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id P.hom y hy
  have : QuasiCompact (fibreStructure j' gb.left y) := by
    rw [fibreStructure_eq_pullback_fst_comp j' gb.left hfU hy]
    infer_instance
  obtain ⟨hiffF, htrF⟩ :=
    canonicalCompactSupportLefschetzNumber_fibre_eq Λ kbar p q hcard j' gb y K J ψ
  have hW := hiffF.1 hXy
  obtain ⟨_, htr⟩ := stalkTrace_directImage_eq_fibre Λ kbar p q hcard gb J hJ y hstalk hW
  let := @Fintype.ofFinite _ (finite_rationalPoints (fibreStructure j' gb.left y))
  let E := rationalPointsFibreEquiv j' gb.left P.hom fU hfU y hy
  refine htr.trans ((htrF hXy hW).symm.trans (heqy.trans ?_))
  rw [finsum_eq_sum_of_fintype, ← Equiv.sum_comp E]
  exact Fintype.sum_congr _ _ fun x' => (stalkTrace_inverseImage Λ kbar p q hcard
    (pullback.fst j' (pullback.fst gb.left y)) x'.1 K (hsK (E x').1)).2

/-- **The trace formula through a fibration in curves.** Let `c` be a compactification of `U` with
a proper `ḡ : W ⟶ P` over `k` to a proper `P`, such that `U ⟶ W ⟶ P` factors as `g ≫ ι` with `ι`
injective on points and all fibres of `g` of dimension at most one, and let `J` be a resolution of
`j'_! K` by injectives with `ḡ_* J ∈ D_ctf(P, Λ)`. If the trace formula holds for curves and for
`ḡ_* J` on `P`, it holds for `K` through `c`. -/
theorem canonicalTraceFormula_of_fibration (h₁ : TraceFormulaUpToDim B Λ kbar p q hcard 1)
    {U : B.Scheme} {fU : U.obj ⟶ Spec (.of k)} [QuasiCompact fU] [LocallyOfFiniteType fU]
    [IsSeparated fU] (c : CompactificationOf (Over.mk fU)) {P S : Scheme.{u}}
    {πP : P ⟶ Spec (.of k)} [IsProper πP] (gbs : c.space ⟶ P) [IsProper gbs]
    (hgbs : gbs ≫ πP = c.toBase) (hfU : c.immersion ≫ gbs ≫ πP = fU) (g : U.obj ⟶ S)
    (ι : S ⟶ P) (hι : Function.Injective ι.base) (hj'g : c.immersion ≫ gbs = g ≫ ι)
    (hfib : ∀ z, topologicalKrullDim (g.fiber z) ≤ 1)
    {K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj)}
    (hK : IsCtf B U Λ (DerivedCategory.Q.obj K.obj))
    {J : CochainComplex.Plus (EtaleModules.{u, 0} Λ c.space)}
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ c.immersion).mapCochainComplexPlus.obj K ⟶ J)
    [QuasiIso ψ.hom] (hJ : ∀ n, Injective (J.obj.X n)) (hSpec : B.Contains (Spec (.of k)))
    (hPB : B.Contains P) (hctf : IsCtf B ⟨P, hPB⟩ Λ (DerivedCategory.Q.obj
      ((etaleModuleDirectImage.{u, 0} Λ gbs).mapCochainComplexPlus.obj J).obj))
    (hP : CanonicalTraceFormula Λ kbar p q hcard πP (CompactificationOf.ofProper πP)
      ((etaleModuleDirectImage.{u, 0} Λ gbs).mapCochainComplexPlus.obj J)) :
    CanonicalTraceFormula Λ kbar p q hcard fU c K := by
  classical
  let gb : Over.mk c.toBase ⟶ Over.mk πP := Over.homMk gbs hgbs
  have : IsProper gb.left := inferInstanceAs (IsProper gbs)
  let C := (etaleModuleDirectImage.{u, 0} Λ gbs).mapCochainComplexPlus.obj J
  obtain ⟨hXP, hsP, heqP⟩ := hP
  let eId := etaleModuleExtensionByZeroIdMapCochainComplexPlusIso Λ P C
  have hPo := isPerfect_frobeniusRestriction_of_iso Λ (Over.mk πP) kbar eId hXP
  obtain ⟨hiffD, htrD⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper_of_torsion Λ
      (fun _ E => torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E) gb kbar p q
      hcard J hJ
  have hWJ := hiffD.1 hPo
  have hX := (isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (Over.mk c.toBase) kbar ψ).2 hWJ
  have hLHS : canonicalCompactSupportLefschetzNumber.{u, 0} Λ fU c kbar p q hcard K hX =
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ πP (CompactificationOf.ofProper πP) kbar p q
        hcard C hXP :=
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
      (Over.mk c.toBase) kbar p q hcard ψ hX hWJ).trans ((htrD hPo hWJ).symm.trans
        (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk πP) kbar p q
          hcard eId hXP hPo).symm)
  have perY := fun y : rationalPoints πP => exists_canonicalTraceFormula_fibre kbar p q hcard h₁
    U c.immersion gbs πP hfU g ι hι hj'g hfib y.1 y.2 K hK
  let ptOf : rationalPoints fU → rationalPoints πP := fun x =>
    ⟨x.1 ≫ c.immersion ≫ gbs, by simpa only [Category.assoc, hfU] using x.2⟩
  have hsK : ∀ x : rationalPoints fU, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K)) := fun x => by
    obtain ⟨-, -, hsy, -⟩ := perY (ptOf x)
    let x' := (rationalPointsFibreEquiv c.immersion gbs πP fU hfU _ (ptOf x).2).symm ⟨x, rfl⟩
    exact (pullback.lift_fst _ _ _ : x'.1 ≫ pullback.fst c.immersion
      (pullback.fst gbs (ptOf x).1) = x.1) ▸ isPerfect_stalk_of_inverseImage Λ kbar
      (pullback.fst c.immersion (pullback.fst gbs (ptOf x).1)) x'.1 K (hsy x')
  refine ⟨hX, hsK, ?_⟩
  let := @Fintype.ofFinite (rationalPoints πP) (finite_rationalPoints πP)
  let := @Fintype.ofFinite (rationalPoints fU) (finite_rationalPoints fU)
  have key : ∀ y : rationalPoints πP, perfectDerivedTrace Λ ⟨_, hsP y⟩ (DerivedCategory.Q.map
      (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y.1 C)) =
      ∑ x : {x : rationalPoints fU // ptOf x = y}, perfectDerivedTrace Λ ⟨_, hsK x.1⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1.1 K)) :=
    fun y => by
      refine (stalkTrace_directImage_eq_sum_fibre kbar p q hcard c.immersion gb hfU K J ψ hJ y.1
        y.2 (fun s => isPerfect_stalkComplex_of_isCtf B ⟨Spec (.of k), hSpec⟩ Λ _
          (isCtf_inverseImage B Λ y.1 hSpec _ _ hctf) s) (perY y).2 hsK (hsP y)).trans ?_
      exact Fintype.sum_equiv (Equiv.subtypeEquivRight
        (p := fun x : rationalPoints fU => x.1 ≫ c.immersion ≫ gb.left = y.1)
        (q := fun x => ptOf x = y) fun x =>
          ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩) _ _ fun _ => rfl
  rw [hLHS, heqP, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Fintype.sum_fiberwise ptOf (fun x => perfectDerivedTrace Λ ⟨_, hsK x⟩
    (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)))

/-- **The fibration step of the trace formula in any dimension.** If the trace formula holds up
to dimension `n` and for curves, it holds on every scheme fibred in curves over `𝔸^n_k`. -/
theorem fibredTraceFormula (hCTF : DirectImagePreservesCtf B Λ k) (n : ℕ)
    (hn : TraceFormulaUpToDim B Λ kbar p q hcard n)
    (h₁ : TraceFormulaUpToDim B Λ kbar p q hcard 1) :
    FibredTraceFormula B Λ kbar p q hcard n := by
  intro U fU _ _ _ g hg hfib j K hK
  let P := projectiveSpaceOverRing n (.of k)
  let πP : P ⟶ Spec (.of k) := P ↘ Spec (.of k)
  let ι := mvPolynomialChart k n
  have hψ : (g ≫ ι) ≫ πP = fU := by
    rw [Category.assoc, mvPolynomialChart_over, hg]
  let c := j.graph πP (g ≫ ι) hψ
  rw [canonicalTraceFormula_iff_of_compactifications Λ
    (fun _ E => torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E) kbar p q hcard fU
    j c K]
  let gbs := CompactificationOf.graphSnd j πP (g ≫ ι) hψ
  have hj'g : c.immersion ≫ gbs = g ≫ ι := CompactificationOf.immersion_graphSnd j πP (g ≫ ι) hψ
  have : EnoughInjectives (EtaleModules.{u, 0} Λ c.space) :=
    etaleModules_enoughInjectives.{u, 0} Λ c.space
  obtain ⟨J, ψJ, hψJ, hJ, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ c.space))
    ((etaleModuleExtensionByZero.{u, 0} Λ c.immersion).mapCochainComplexPlus.obj K) (𝟙 _)
  have hSpec : B.Contains (Spec (.of k)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of k) U.property
      ((Cardinal.mk_le_aleph0).trans (U.obj.aleph0_le_size.trans (Cardinal.self_le_power _
        Cardinal.one_le_aleph0)))
  have hPB : B.Contains P := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact πP hSpec
  have : IsProper (gbs ≫ πP) := by
    rw [CompactificationOf.graphSnd_toBase]
    infer_instance
  have hctf := hCTF ⟨c.space, Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact c.toBase hSpec⟩
    ⟨P, hPB⟩ U πP gbs c.immersion (by
      rw [hj'g]
      exact topologicalKrullDim_comp_fiber_le_one g ι ι.isOpenEmbedding.injective hfib)
    K hK J ψJ hψJ hJ
  exact canonicalTraceFormula_of_fibration kbar p q hcard h₁ c gbs
    (CompactificationOf.graphSnd_toBase j πP (g ≫ ι) hψ) (by rw [← Category.assoc, hj'g, hψ]) g ι
    ι.isOpenEmbedding.injective hj'g hfib hK ψJ hJ hSpec hPB hctf
    (hn ⟨P, hPB⟩ πP (topologicalKrullDim_projectiveSpaceOverRing k n).le
      (CompactificationOf.ofProper πP)
      ((etaleModuleDirectImage.{u, 0} Λ gbs).mapCochainComplexPlus.obj J) hctf)

/-- **The trace formula in any dimension, from the curve case.** If proper direct images of
extensions by zero along curve fibrations preserve `D_ctf` and the trace formula holds for curves,
it holds for every separated scheme of finite type over `k` in `B`, through every
compactification, for every `K ∈ D_ctf(X, Λ)`. -/
theorem canonicalTraceFormula_of_curves (hCTF : DirectImagePreservesCtf B Λ k)
    (h₁ : TraceFormulaUpToDim B Λ kbar p q hcard 1) (X : B.Scheme) (f : X.obj ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K :=
  canonicalTraceFormula_of_forall_traceFormulaUpToDim
    (traceFormulaUpToDim_of_fibred h₁ fun n hn => fibredTraceFormula kbar p q hcard hCTF n hn h₁)
    X f j K hK

end Stacks.EtaleCohomology

end
