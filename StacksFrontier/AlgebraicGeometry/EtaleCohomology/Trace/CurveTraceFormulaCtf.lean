module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalTraceFormulaQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CtfPerfectStalks

/-!
# The trace formula for an object of `D_ctf` on a curve, from the core

Let `X` be a separated scheme of finite type and dimension at most one over a finite field `k`,
`j : X ⟶ X̄` a compactification, `Λ` a finite ring with `#Λ ∈ k^*`, and `K` a bounded below
complex of sheaves of `Λ`-modules on `X_étale` whose class lies in `D_ctf(X, Λ)`
(`Stacks.EtaleCohomology.IsCtf`). Then `Stacks.EtaleCohomology.CurveTraceCore` gives the trace
formula of [Stacks, Tag 03UG] for `K`: `RΓ_c(X_k̄, K)` is perfect and
`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`.

The class of `K` is represented by a bounded complex `C` of constructible flat sheaves; an
isomorphism `Q(C) ≅ Q(K)` in the derived category is a zigzag `C ⟶ I ⟵ K` of quasi-isomorphisms
into a bounded below complex of injectives (morphisms into a K-injective complex all come from
chain maps). In the namespace `Stacks.EtaleCohomology`, the trace formula is invariant under
quasi-isomorphism (`cohomologicalTraceFormula_iff_of_quasiIso`), and holds for `C`
(`cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_constructibleFlat_complex`).

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there, as is `Stacks.EtaleCohomology.IsCtf`.

## Main results

* `CochainComplex.exists_quasiIso_zigzag_of_Q_iso`
* `Stacks.EtaleCohomology.exists_constructibleFlat_zigzag_of_isCtf`
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf`
* `Stacks.EtaleCohomology.perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace CochainComplex

/-- **An isomorphism in the derived category between bounded below complexes is a zigzag of
quasi-isomorphisms** `C ⟶ I ⟵ K` into a bounded below complex of injectives. -/
theorem exists_quasiIso_zigzag_of_Q_iso {A : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory A] (C K : CochainComplex.Plus A)
    (e : DerivedCategory.Q.obj C.obj ≅ DerivedCategory.Q.obj K.obj) :
    ∃ (I : CochainComplex.Plus A) (s : C ⟶ I) (t : K ⟶ I), QuasiIso s.hom ∧ QuasiIso t.hom := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsGE a := inferInstance
  obtain ⟨R, -, hR⟩ := exists_injectiveResolution_isStrictlyGE a K.obj
  have : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective _ a
  have : QuasiIso R.ι := inferInstance
  let e' := e ≪≫ asIso (DerivedCategory.Q.map R.ι)
  obtain ⟨g, hg⟩ := DerivedCategory.Q_map_surjective_of_isKInjective C.obj R.cocomplex e'.hom
  have hgq : QuasiIso g := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hg]
    infer_instance
  exact ⟨⟨R.cocomplex, R.boundedBelow⟩, ObjectProperty.homMk g, ObjectProperty.homMk R.ι, hgq,
    inferInstanceAs (QuasiIso R.ι)⟩

end CochainComplex

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- Extension by zero along an open immersion preserves quasi-isomorphisms of bounded below
complexes: it is exact. -/
theorem quasiIso_extensionByZero_map {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)} (φ : K ⟶ K') [QuasiIso φ.hom] :
    QuasiIso ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.map φ).hom := by
  have : PreservesFiniteColimits (etaleModuleExtensionByZero.{u, 0} Λ j) :=
    have : (etaleModuleExtensionByZero.{u, 0} Λ j).IsLeftAdjoint :=
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).isLeftAdjoint
    inferInstance
  exact inferInstanceAs (QuasiIso (((etaleModuleExtensionByZero.{u, 0} Λ j).mapHomologicalComplex
    (ComplexShape.up ℤ)).map φ.hom))

variable [Finite Λ]

omit [Finite Λ] in
/-- **An object of `D_ctf` is a zigzag of quasi-isomorphisms away from a bounded complex of
constructible flat sheaves**: for a bounded below `K` whose class lies in `D_ctf(X, Λ)`, there are
a complex `C` concentrated in degrees `[a, a + N]` with constructible flat terms and
quasi-isomorphisms `C ⟶ I ⟵ K`. -/
theorem exists_constructibleFlat_zigzag_of_isCtf (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX : B.Contains X) (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) :
    ∃ (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a : ℤ) (N : ℕ)
      (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (s : C ⟶ I) (t : K ⟶ I),
      QuasiIso s.hom ∧ QuasiIso t.hom ∧ (∀ n, n < a → IsZero (C.obj.X n)) ∧
        (∀ n, a + N < n → IsZero (C.obj.X n)) ∧
        ∀ n, IsConstructibleFlatEtaleModule B (B.obj X hX) Λ (C.obj.X n) := by
  have h := hK (B.obj X hX) (𝟙 _) inferInstance inferInstance
  rw [inclusion_map_id_of_contains] at h
  obtain ⟨C, a, b, hGE, hLE, hflat, ⟨eC⟩⟩ := h
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ (𝟙 X)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ (𝟙 X)
  let eK : ((etaleModuleInverseImage.{u, 0} Λ (𝟙 X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ≅ K.obj :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => (etaleModuleInverseImageIdIso Λ X).app (K.obj.X n))
      (fun i j _ => ((etaleModuleInverseImageIdIso Λ X).hom.naturality (K.obj.d i j)).symm)
  let eId : (etaleModuleRingDerivedInverseImage.{u, 0} Λ (𝟙 X)).obj (DerivedCategory.Q.obj K.obj) ≅
      DerivedCategory.Q.obj K.obj :=
    (etaleModuleInverseImage.{u, 0} Λ (𝟙 X)).mapDerivedCategoryFactors.app K.obj ≪≫
      DerivedCategory.Q.mapIso eK
  let C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X) := ⟨C, ⟨a, hGE⟩⟩
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  obtain ⟨I, s, t, hs, ht⟩ := CochainComplex.exists_quasiIso_zigzag_of_Q_iso C' K (eC ≪≫ eId)
  exact ⟨C', a, (b - a).toNat, I, s, t, hs, ht,
    fun n hn => CochainComplex.isZero_of_isStrictlyGE C a n hn,
    fun n hn => CochainComplex.isZero_of_isStrictlyLE C b n (by omega), hflat⟩

/-- A scheme of finite type over a Noetherian ring is locally Noetherian and Noetherian. -/
private theorem isLocallyNoetherian_and_isNoetherian_of_finiteType
    {X : Scheme.{u}} {R : CommRingCat.{u}} [IsNoetherianRing R] (f : X ⟶ Spec R)
    [LocallyOfFiniteType f] [QuasiCompact f] : IsLocallyNoetherian X ∧ IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  ⟨‹_›, { }⟩

/-- **The trace formula `T''(X̄, j_! K) = T'(X̄, j_! K)` for an object of `D_ctf` on a curve, from
the core.** Let `X` be a separated scheme of finite type and dimension at most one over `k` (it
need not be dense in `X̄`, and may be empty or of dimension zero), lying in the big étale site
`B`, with a compactification `j : X ⟶ X̄`, and `K` a bounded below complex with perfect stalks
whose class lies in `D_ctf(X, Λ)`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hX : B.Contains X)
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) (hKs : HasPerfectStalks Λ K) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNoetherian_of_finiteType f
  obtain ⟨C, a, N, I, s, t, hs, ht, hlo, hhi, hflat⟩ :=
    exists_constructibleFlat_zigzag_of_isCtf Λ B K hX hK
  have hIs : HasPerfectStalks Λ I := (hasPerfectStalks_iff_of_quasiIso t).1 hKs
  have hCs : HasPerfectStalks Λ C := (hasPerfectStalks_iff_of_quasiIso s).2 hIs
  have hC :=
    cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_constructibleFlat_complex Λ kbar
      p q hcard hcore B (B.obj X hX) f hdim J C hCs a N hlo hhi hflat
  have := quasiIso_extensionByZero_map Λ J.immersion s
  have := quasiIso_extensionByZero_map Λ J.immersion t
  exact (cohomologicalTraceFormula_iff_of_quasiIso kbar p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.map t) _
      (hasPerfectStalks_extensionByZero Λ J.immersion I hIs)).2
    ((cohomologicalTraceFormula_iff_of_quasiIso kbar p q hcard
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.map s) _
        (hasPerfectStalks_extensionByZero Λ J.immersion I hIs)).1 hC)

/-- **The trace formula of [Stacks, Tag 03UG] for an object of `D_ctf` on a curve, from the core.**
Let `X` be a separated scheme of finite type and dimension at most one over `k`, lying in the big
étale site `B`, with a compactification `j : X ⟶ X̄`, and `K` a bounded below complex whose class
lies in `D_ctf(X, Λ)`. Then `RΓ_c(X_k̄, K)` is perfect and
`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ^♮`; the stalks `K_x̄` are perfect
by `Stacks.EtaleCohomology.hasPerfectStalks_of_isCtf`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [Fintype (rationalPoints f)] (hdim : topologicalKrullDim X ≤ 1)
    (J : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX : B.Contains X) (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) :
    ∃ (hKs : HasPerfectStalks Λ K) (hperf : StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K))),
      perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard K)) =
        ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hKs (rationalGeometricPoint kbar x.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNoetherian_of_finiteType f
  have hKs := hasPerfectStalks_of_isCtf B hX Λ K hK
  exact ⟨hKs,
    perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_cohomologicalTraceFormula Λ kbar
      p q hcard f J K hKs
    (cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf Λ kbar p q hcard hcore B f
      hdim J K hX hK hKs)⟩

end Standard

end Stacks.EtaleCohomology

end
