module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.RingTheory.Module.DualCokernel.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenCharacterisation
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBettiGeneration
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
import all StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.SingularLocus

/-!
# Charts for the bottom cohomology of a perfect complex

Let `X` be a scheme and `E` an object of `D(𝒪_X)` which is perfect of Tor amplitude in `[a, b]`.
Every point of `X` lies in an affine chart `Spec R ⟶ X`, an open immersion, along which `E` is
the derived sheafification of a bounded complex `P` of finite free `R`-modules concentrated in
degrees `[a, b]`. On such a chart the bottom cohomology of the derived pullback of `E` along any
`Spec S ⟶ Spec R` is the kernel of the base change of the bottom differential of `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable {X : Scheme.{u}}

/-- **A Tor amplitude bound below survives every derived pullback.** If `E` has Tor amplitude in
`[a, b]` then `Lf^* E` has no cohomology below degree `a`, for every morphism of schemes `f`.

`E` is represented by a bounded complex of flat modules concentrated in `[a, b]` ([stacks 08CI]),
which is K-flat ([stacks 06YQ]) and therefore computes the derived pullback ([stacks 06YJ]); its
degreewise pullback still vanishes below degree `a`. -/
theorem isGE_derivedPullback_of_hasTorAmplitude (E : DerivedCategory X.Modules) (a b : ℤ)
    (hE : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    ((derivedPullback f.toLRSHom.toShHom).obj E).IsGE a := by
  have hE' : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a (max a b) :=
    fun F i hi => hE F i fun h => hi ⟨h.1, h.2.trans (le_max_right _ _)⟩
  open Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative in
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
    exists_flat_representative_of_hasTorAmplitude E a (max a b) (le_max_left _ _) hE'
  have hK : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace K :=
    RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat _ K
      ⟨max a b, (CochainComplex.isStrictlyLE_iff K _).2 fun i hi =>
        hzero i fun h => (not_le.2 hi) h.2⟩ hflat
  let L := ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  have hL : CochainComplex.IsStrictlyGE L a :=
    (CochainComplex.isStrictlyGE_iff L a).2 fun i hi =>
      Functor.map_isZero _ (hzero i fun h => (not_le.2 hi) h.1)
  have e₁ : (derivedPullback f.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj L :=
    (derivedPullback f.toLRSHom.toShHom).mapIso
        (e.symm ≪≫ ((DerivedCategory.quotientCompQhIso _).app K).symm) ≪≫
      @asIso _ _ _ _ ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
        (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
          f.toLRSHom.toShHom K hK) ≪≫
      (DerivedCategory.quotientCompQhIso _).app L
  exact DerivedCategory.TStructure.t.isGE_of_iso e₁.symm a

/-- **The derived-fibre Betti numbers of `E` vanish below the Tor amplitude bound.** -/
theorem derivedFiberBetti_eq_zero_of_lt (E : DerivedCategory X.Modules)
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (a b : ℤ)
    (hE : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b) (x : X) {i : ℤ}
    (hi : i < a) : DerivedFibreBetti.derivedFiberBetti X E hPC i x = 0 := by
  rw [DerivedFibreBetti.derivedFiberBetti_apply]
  have := isGE_derivedPullback_of_hasTorAmplitude E a b hE (X.fromSpecResidueField x)
  have : Subsingleton ((moduleSpecΓFunctor (R := X.residueField x)).obj
      ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules i).obj
        ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E))) :=
    ModuleCat.subsingleton_of_isZero ((moduleSpecΓFunctor (R := X.residueField x)).map_isZero
      (DerivedCategory.isZero_of_isGE
        ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E) a i hi))
  exact Module.finrank_zero_of_subsingleton

/-- **A chart for `E` in degree `a`.** An open immersion `ι : Spec R ⟶ X` together with a
bounded complex `P` of finite free `R`-modules concentrated in degrees `≥ a` and an
identification of the derived pullback of `E` along `ι` with the derived sheafification of `P`. -/
structure Chart (E : DerivedCategory X.Modules) (a : ℤ) : Type (u + 1) where
  /-- The ring of the chart. -/
  R : CommRingCat.{u}
  /-- The chart, an open immersion. -/
  ι : Spec R ⟶ X
  /-- The morphism `ι` is an open immersion. -/
  isOpenImmersion : IsOpenImmersion ι
  /-- The complex representing `E` on the chart. -/
  P : CochainComplex (ModuleCat.{u} R) ℤ
  /-- An upper bound for the degrees of `P`. -/
  b : ℤ
  /-- The complex `P` vanishes in degrees below `a`. -/
  isStrictlyGE : CochainComplex.IsStrictlyGE P a
  /-- The complex `P` vanishes in degrees above `b`. -/
  isStrictlyLE : CochainComplex.IsStrictlyLE P b
  /-- Each term of `P` is a free `R`-module. -/
  free (i : ℤ) : Module.Free R (P.X i)
  /-- Each term of `P` is a finite `R`-module. -/
  finite (i : ℤ) : Module.Finite R (P.X i)
  /-- The identification of `E` on the chart with the derived sheafification of `P`. -/
  iso : (derivedPullback ι.toLRSHom.toShHom).obj E ≅
    (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)

attribute [instance] Chart.isOpenImmersion Chart.isStrictlyGE Chart.isStrictlyLE Chart.free
  Chart.finite

/-- **The affine step of the chart construction.** On `Spec R`, a perfect object `E'` is, on a
principal open neighbourhood `Spec R_g` of a given point `p`, the derived sheafification of a
bounded above complex of finite free `R_g`-modules whose term in degree `i` has rank `β_i(p)`.

`E'` is the derived sheafification of a perfect complex `M` of `R`-modules ([stacks 08EB]); the
local structure theorem [stacks 0BCD] represents `M ⊗ᴸ R_g` by such a complex, the ranks being
the derived-fibre Betti numbers, and [stacks 08DW] part (2) carries the representation to the
derived pullback. -/
theorem exists_away_iso_mapDerivedCategory_tilde (R : CommRingCat.{u})
    (E' : DerivedCategory (Spec R).Modules)
    (hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E')
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E')
    (p : Spec R) :
    ∃ (g : (R : Type u)) (_ : g ∉ p.asIdeal)
      (P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ) (b₀ : ℤ),
      CochainComplex.IsStrictlyLE P b₀ ∧
      (∀ i : ℤ, Nonempty (P.X i ≃ₗ[Localization.Away g]
        (Fin (DerivedFibreBetti.derivedFiberBetti (Spec R) E' hPC i p) →
          Localization.Away g))) ∧
      Nonempty ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u)
          (Localization.Away g)))).toLRSHom.toShHom).obj E' ≅
        (tilde.functor (CommRingCat.of (Localization.Away g))).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)) := by
  classical
  obtain ⟨M, hMperf, ⟨eM⟩⟩ := exists_isPerfect_iso_mapDerivedCategory_tilde R E' hE' hPC
  have hbetti : ∀ i : ℤ, StacksDraft.Perfect.fibreBetti.{u, u} M i p =
      DerivedFibreBetti.derivedFiberBetti (Spec R) E' hPC i p := fun i =>
    (derivedFiberBetti_eq_fibreBetti_of_iso R M E' hPC eM i p).symm
  have : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨-, -, g, hg, P, -, b₀, -, hle, hX, ⟨eP⟩⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing.{u, u} p.asIdeal M hMperf
  refine ⟨g, hg, P, b₀, hle, fun i => ?_, ⟨?_⟩⟩
  · obtain ⟨e⟩ := hX i
    exact ⟨e.toLinearEquiv.trans (ULift.moduleEquiv.trans
      (LinearEquiv.funCongrLeft _ _ (finCongr (hbetti i)).symm))⟩
  · exact (derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u)
        (Localization.Away g)))).toLRSHom.toShHom).mapIso eM.symm ≪≫
      (StandardModel.affinePullbackComparison R (CommRingCat.of (Localization.Away g))
        (CommRingCat.ofHom (algebraMap (R : Type u) (Localization.Away g)))).app M ≪≫
      (tilde.functor (CommRingCat.of (Localization.Away g))).mapDerivedCategory.mapIso eP.symm

/-- Restriction along a composite `Spec.map φ ≫ j` is the derived pullback along `Spec.map φ` of
the derived pullback along `j`. -/
def derivedPullbackCompObjIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') (j : Spec R ⟶ X)
    (E : DerivedCategory X.Modules) :
    (derivedPullback (Spec.map φ ≫ j).toLRSHom.toShHom).obj E ≅
      (derivedPullback (Spec.map φ).toLRSHom.toShHom).obj
        ((derivedPullback j.toLRSHom.toShHom).obj E) :=
  eqToIso (congrArg (fun k => (derivedPullback k).obj E)
      (comp_toLRSHom_toShHom (Spec.map φ) j)) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (Spec.map φ).toLRSHom.toShHom j.toLRSHom.toShHom).app E).symm

/-- A complex whose term in degree `i` is free of rank `n i`, with `n i = 0` below `a`, is
concentrated in degrees `≥ a`. -/
theorem isStrictlyGE_of_linearEquiv {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ → ℕ)
    (e : ∀ i : ℤ, Nonempty (P.X i ≃ₗ[R] (Fin (n i) → R))) (a : ℤ)
    (h : ∀ i : ℤ, i < a → n i = 0) : CochainComplex.IsStrictlyGE P a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨e⟩ := e i
  have : IsEmpty (Fin (n i)) := by
    rw [h i hi]
    infer_instance
  have : Subsingleton (P.X i) := e.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- The derived-fibre Betti numbers of a derived pullback, pointwise. -/
theorem derivedFiberBetti_derivedPullback_apply {Y : Scheme.{u}} (f : Y ⟶ X)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (i : ℤ) (y : Y) :
    DerivedFibreBetti.derivedFiberBetti Y ((derivedPullback f.toLRSHom.toShHom).obj E)
        (DerivedFibreBetti.isPseudoCoherent_derivedPullback f E hE) i y =
      DerivedFibreBetti.derivedFiberBetti X E hE i (f.base y) :=
  congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback f E hE i) y

/-- **Every point lies in a chart whose terms have the derived-fibre Betti numbers as ranks.**
For `E` perfect of Tor amplitude in `[a, b]`, each point `x` of `X` lies in the image of a chart
for `E` in degree `a`, chosen so that the term of `P` in degree `i` is free of rank `β_i(x)`.

The point is taken inside an affine open `Spec Γ(X, V)` and
`exists_away_iso_mapDerivedCategory_tilde` applies there; the ranks vanish below `a` by
`derivedFiberBetti_eq_zero_of_lt`. -/
theorem Chart.exists_mem (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (a b : ℤ)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b) (x : X) :
    ∃ (c : Chart E a) (y : Spec c.R), c.ι.base y = x ∧ ∀ i : ℤ,
      Nonempty (c.P.X i ≃ₗ[c.R] (Fin (DerivedFibreBetti.derivedFiberBetti X E
        (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) i x) → c.R)) := by
  classical
  set hPC := Scheme.Modules.isPseudoCoherent_of_isPerfect E hE
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  obtain ⟨y, hy⟩ : x ∈ Set.range (V.2.fromSpec).base := by
    rwa [V.2.range_fromSpec]
  have : IsOpenImmersion (V.2.fromSpec) := V.2.isOpenImmersion_fromSpec
  have hchartPerf := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (V.2.fromSpec).toLRSHom.toShHom E hE
  have hchartPC := DerivedFibreBetti.isPseudoCoherent_derivedPullback V.2.fromSpec E hPC
  obtain ⟨g, hg, P, b₀, hle, hrank, ⟨eP⟩⟩ :=
    exists_away_iso_mapDerivedCategory_tilde Γ(X, V.1) _ hchartPerf hchartPC y
  have hbc (i : ℤ) : DerivedFibreBetti.derivedFiberBetti (Spec Γ(X, V.1))
      ((derivedPullback (V.2.fromSpec).toLRSHom.toShHom).obj E) hchartPC i y =
      DerivedFibreBetti.derivedFiberBetti X E hPC i x := by
    rw [derivedFiberBetti_derivedPullback_apply, hy]
  let φ : Γ(X, V.1) ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g))
  have : IsOpenImmersion (Spec.map φ) := Scheme.isOpenImmersion_SpecMap_localizationAway g
  have hrank' (i : ℤ) : Nonempty (P.X i ≃ₗ[Localization.Away g]
      (Fin (DerivedFibreBetti.derivedFiberBetti X E hPC i x) → Localization.Away g)) := by
    obtain ⟨e⟩ := hrank i
    exact ⟨e.trans (LinearEquiv.funCongrLeft _ _ (finCongr (hbc i)).symm)⟩
  let c : Chart E a :=
    { R := CommRingCat.of (Localization.Away g)
      ι := Spec.map φ ≫ V.2.fromSpec
      isOpenImmersion := IsOpenImmersion.comp _ _
      P := P
      b := b₀
      isStrictlyGE := isStrictlyGE_of_linearEquiv P _ hrank' a fun i hi =>
        derivedFiberBetti_eq_zero_of_lt E hPC a b htor x hi
      isStrictlyLE := hle
      free := fun i => Module.Free.of_equiv (hrank' i).some.symm
      finite := fun i => Module.Finite.equiv (hrank' i).some.symm
      iso := derivedPullbackCompObjIso φ V.2.fromSpec E ≪≫ eP }
  obtain ⟨z, hz⟩ : y ∈ Set.range (Spec.map φ).base := by
    have hb : y ∈ PrimeSpectrum.basicOpen g := hg
    rwa [← Scheme.Hom.opensRange_localizationAway (R := Γ(X, V.1)) g] at hb
  refine ⟨c, z, ?_, hrank'⟩
  have hz' : (Spec.map φ) z = y := hz
  change (Spec.map φ ≫ V.2.fromSpec) z = x
  simpa only [Scheme.Hom.comp_apply, hz'] using hy

/-! ### The bottom cohomology on a chart -/

namespace Chart

variable {E : DerivedCategory X.Modules} {a : ℤ} (c : Chart E a)

/-- The degreewise base change of the complex of a chart along `φ : R ⟶ S`. -/
abbrev baseChange {S : CommRingCat.{u}} (φ : c.R ⟶ S) : CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj c.P

/-- The bottom differential of the complex of a chart. -/
abbrev d : c.P.X a ⟶ c.P.X ((ComplexShape.up ℤ).next a) := c.P.d a ((ComplexShape.up ℤ).next a)

/-- The kernel of the base change along `φ : R ⟶ S` of the bottom differential of a chart. -/
abbrev kernel {S : CommRingCat.{u}} (φ : c.R ⟶ S) : ModuleCat.{u} S :=
  ModuleCat.of S (LinearMap.ker ((ModuleCat.extendScalars.{u, u, u} φ.hom).map c.d).hom)

/-- Derived extension of scalars of the complex of a chart is degreewise extension of scalars:
the complex is bounded above with projective terms. -/
def extendScalarsIso {S : CommRingCat.{u}} (φ : c.R ⟶ S) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ.hom).functor.obj (DerivedCategory.Q.obj c.P) ≅ DerivedCategory.Q.obj (c.baseChange φ) :=
  haveI : ∀ i, Projective (c.P.X i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis c.R (c.P.X i))
  @asIso _ _ _ _ ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ.hom).comparison.app c.P)
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ.hom).comparison_isIso_of_projective c.P c.b)

/-- The derived pullback of `E` along `Spec S ⟶ Spec R ⟶ X` is the derived sheafification of the
degreewise base change of the complex of the chart. -/
def derivedPullbackIso {S : CommRingCat.{u}} (φ : c.R ⟶ S) :
    (derivedPullback (Spec.map φ ≫ c.ι).toLRSHom.toShHom).obj E ≅
      (tilde.functor S).mapDerivedCategory.obj (DerivedCategory.Q.obj (c.baseChange φ)) :=
  derivedPullbackCompObjIso φ c.ι E ≪≫
    (derivedPullback (Spec.map φ).toLRSHom.toShHom).mapIso c.iso ≪≫
    (StandardModel.affinePullbackComparison c.R S φ).app (DerivedCategory.Q.obj c.P) ≪≫
    (tilde.functor S).mapDerivedCategory.mapIso (c.extendScalarsIso φ)

end Chart

/-- Cohomology of a derived sheafification is the sheafification of cohomology. -/
def homologyTildeIso {S : CommRingCat.{u}} (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Spec S).Modules i).obj
        ((tilde.functor S).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      (tilde.functor S).obj (K.homology i) :=
  ((tilde.functor S).mapDerivedCategoryHomologyFunctorIso i).app (DerivedCategory.Q.obj K) ≪≫
    (tilde.functor S).mapIso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app K)

/-- The bottom cohomology of a complex of modules concentrated in degrees `≥ a` is the kernel of
its bottom differential. -/
def homologyIsoKerOfIsStrictlyGE {S : Type u} [Ring S] (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (a : ℤ) [K.IsStrictlyGE a] :
    K.homology a ≅ ModuleCat.of S (LinearMap.ker (K.d a ((ComplexShape.up ℤ).next a)).hom) :=
  (K.isoHomologyπ (a - 1) a (by simp)
    ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).symm ≪≫
    (K.sc a).moduleCatCyclesIso

namespace Chart

variable {E : DerivedCategory X.Modules} {a : ℤ} (c : Chart E a)

/-- **The bottom cohomology of the derived pullback along a chart point.** For `φ : R ⟶ S`,
`H^a(L(Spec S ⟶ Spec R ⟶ X)^* E)` is the sheaf associated to the kernel of the base change to
`S` of the bottom differential of the chart. -/
def pullbackHomologyIso {S : CommRingCat.{u}} (φ : c.R ⟶ S) :
    pullbackHomology E a (Spec.map φ ≫ c.ι) ≅ (tilde.functor S).obj (c.kernel φ) :=
  (DerivedCategory.homologyFunctor (Spec S).Modules a).mapIso (c.derivedPullbackIso φ) ≪≫
    homologyTildeIso (c.baseChange φ) a ≪≫
    (tilde.functor S).mapIso (homologyIsoKerOfIsStrictlyGE (c.baseChange φ) a)

/-- **Finite local freeness of the bottom cohomology at a chart point is a statement about the
kernel of the base changed bottom differential.** -/
theorem isFiniteLocallyFreeOfRank_pullbackHomology_iff {S : CommRingCat.{u}} (φ : c.R ⟶ S)
    (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (pullbackHomology E a (Spec.map φ ≫ c.ι)) r ↔
      letI := φ.hom.toAlgebra
      Module.IsFiniteLocallyFreeOfRank S (LinearMap.ker (c.d.hom.baseChange S)) r := by
  let := φ.hom.toAlgebra
  have key := tilde_isFiniteLocallyFreeOfRank_iff S (LinearMap.ker (c.d.hom.baseChange S)) r
  exact ⟨fun h => key.1 (h.of_iso (c.pullbackHomologyIso φ)),
    fun h => .of_iso (c.pullbackHomologyIso φ).symm (key.2 h)⟩

end Chart

/-! ### Restriction to opens -/

/-- Restriction along an open immersion is the derived pullback along it, on an object. -/
def derivedRestrictObjIso {W Y : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory Y.Modules) :
    (derivedPullback j.toLRSHom.toShHom).obj K ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K :=
  ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app K).symm

/-- **Bottom cohomology of a derived pullback restricts along open immersions.** For an open
immersion `j : W ⟶ Y`, `H^a(L(j ≫ f)^* E)` is the restriction of `H^a(Lf^* E)` to `W`. -/
def pullbackHomologyRestrictIso (E : DerivedCategory X.Modules) (a : ℤ) {W Y : Scheme.{u}}
    (j : W ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ X) :
    pullbackHomology E a (j ≫ f) ≅ (pullbackHomology E a f).restrict j :=
  (pullbackHomologyCompIso E a j f).symm ≪≫
    (DerivedCategory.homologyFunctor W.Modules a).mapIso
      (derivedRestrictObjIso j ((derivedPullback f.toLRSHom.toShHom).obj E)) ≪≫
    (Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso j a).app _

/-- **Finite local freeness of rank `r` is local along open immersions.** -/
theorem isFiniteLocallyFreeOfRank_of_forall_exists_openImmersion {Y : Scheme.{u}} (G : Y.Modules)
    (r : ℕ) (h : ∀ y : Y, ∃ (W : Scheme.{u}) (j : W ⟶ Y) (_ : IsOpenImmersion j),
      y ∈ Set.range j.base ∧ Scheme.Modules.IsFiniteLocallyFreeOfRank (G.restrict j) r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank G r := by
  choose W j hj hy hG using h
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top (fun y => (j y).opensRange)
    (eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) fun y => ?_
  have e : G.restrict (j y).opensRange.ι ≅
      (G.restrict (j y)).restrict (j y).isoOpensRange.inv :=
    (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (j y)).symm).app G ≪≫
      (Scheme.Modules.restrictFunctorComp _ _).app G
  exact ((hG y).restrict _).of_iso e.symm

/-- Finite local freeness of rank `r` can be checked on the affine opens. -/
private theorem isFiniteLocallyFreeOfRank_of_forall_affineOpens {Y : Scheme.{u}} (G : Y.Modules)
    (r : ℕ) (h : ∀ V : Y.affineOpens, haveI := V.2.isOpenImmersion_fromSpec
      Scheme.Modules.IsFiniteLocallyFreeOfRank (G.restrict V.2.fromSpec) r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank G r := by
  refine isFiniteLocallyFreeOfRank_of_forall_exists_openImmersion G r fun y => ?_
  obtain ⟨V, hyV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top Y).ge (Set.mem_univ y))
  exact ⟨_, V.2.fromSpec, V.2.isOpenImmersion_fromSpec, by rwa [V.2.range_fromSpec], h V⟩

/-! ### The dual cokernel sheaf of a chart -/

namespace Chart

variable {E : DerivedCategory X.Modules} {a : ℤ} (c : Chart E a)

/-- The dual cokernel of the bottom differential of a chart, as a module. -/
abbrev dualCokerModule : ModuleCat.{u} c.R := ModuleCat.of c.R (LinearMap.DualCoker c.d.hom)

/-- **The dual cokernel sheaf of a chart.** The quasi-coherent sheaf on `Spec R` associated to
the cokernel of the transpose of the bottom differential of the chart. -/
abbrev dualCoker : (Spec c.R).Modules := (tilde.functor c.R).obj c.dualCokerModule

/-- The dual cokernel sheaf of a chart is of finite presentation. -/
instance : c.dualCoker.IsFinitePresentation :=
  (tilde_isFinitePresentation_iff c.dualCokerModule).2
    (inferInstanceAs (Module.FinitePresentation c.R (LinearMap.DualCoker c.d.hom)))

/-- The dual cokernel sheaf of a chart is of finite type. -/
instance : c.dualCoker.IsFiniteType :=
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation c.dualCoker

/-- The dual cokernel sheaf of a chart is quasi-coherent. -/
instance : c.dualCoker.IsQuasicoherent :=
  SheafOfModules.instIsQuasicoherentOfIsFinitePresentation c.dualCoker

/-- Finite local freeness of the pullback of the dual cokernel sheaf to an affine scheme is that
of the base changed dual cokernel. -/
theorem isFiniteLocallyFreeOfRank_pullback_dualCoker_iff {S : CommRingCat.{u}} (φ : c.R ⟶ S)
    (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank
        ((Scheme.Modules.pullback (Spec.map φ)).obj c.dualCoker) r ↔
      letI := φ.hom.toAlgebra
      Module.IsFiniteLocallyFreeOfRank S (S ⊗[c.R] LinearMap.DualCoker c.d.hom) r := by
  let := φ.hom.toAlgebra
  have e := (pullbackTildeIso c.R S φ).app c.dualCokerModule
  have key := tilde_isFiniteLocallyFreeOfRank_iff S (S ⊗[c.R] LinearMap.DualCoker c.d.hom) r
  exact ⟨fun h => key.1 (h.of_iso e), fun h => .of_iso e.symm (key.2 h)⟩

/-- Pullback along `Spec S ⟶ T ⟶ Spec R` of the dual cokernel sheaf, read through the ring map
of the composite. -/
def pullbackDualCokerIso {T : Scheme.{u}} {S : CommRingCat.{u}} (j : Spec S ⟶ T)
    (t : T ⟶ Spec c.R) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback t).obj c.dualCoker) ≅
      (Scheme.Modules.pullback (Spec.map (Spec.preimage (j ≫ t)))).obj c.dualCoker :=
  (Scheme.Modules.pullbackComp j t).app c.dualCoker ≪≫
    (Scheme.Modules.pullbackCongr (Spec.map_preimage (j ≫ t)).symm).app c.dualCoker

/-- Local freeness of the pullback of the dual cokernel along `t : T ⟶ Spec R` can be checked on
the affine opens `Spec S` of `T`: the bottom cohomology there must be locally free of rank `r`, and
the kernels of the base changes to the residue fields must have dimension at most `r`. -/
private theorem isFiniteLocallyFreeOfRank_pullback_dualCoker_of_forall_affineOpens {T : Scheme.{u}}
    (t : T ⟶ Spec c.R) (r : ℕ)
    (hker : ∀ (V : T.affineOpens) [IsOpenImmersion V.2.fromSpec],
      Scheme.Modules.IsFiniteLocallyFreeOfRank (pullbackHomology E a (V.2.fromSpec ≫ t ≫ c.ι)) r)
    (hfib : ∀ (V : T.affineOpens) (p : Ideal Γ(T, V.1)) [p.IsMaximal],
      letI := (Spec.preimage (V.2.fromSpec ≫ t) ≫
        CommRingCat.ofHom (algebraMap Γ(T, V.1) p.ResidueField)).hom.toAlgebra
      Module.finrank p.ResidueField (LinearMap.ker (c.d.hom.baseChange p.ResidueField)) ≤ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback t).obj c.dualCoker) r := by
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  refine isFiniteLocallyFreeOfRank_of_forall_affineOpens _ r fun V => ?_
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  set φ := Spec.preimage (V.2.fromSpec ≫ t)
  refine Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    (((Scheme.Modules.restrictFunctorIsoPullback V.2.fromSpec).app _) ≪≫
      c.pullbackDualCokerIso V.2.fromSpec t).symm ?_
  rw [c.isFiniteLocallyFreeOfRank_pullback_dualCoker_iff φ r]
  let := φ.hom.toAlgebra
  refine LinearMap.isFiniteLocallyFreeOfRank_baseChange_dualCoker _ c.d.hom ?_ fun p _ => ?_
  · have hmor : Spec.map φ ≫ c.ι = V.2.fromSpec ≫ t ≫ c.ι := by
      rw [Spec.map_preimage, Category.assoc]
    have := hker V
    rw [← hmor] at this
    exact (c.isFiniteLocallyFreeOfRank_pullbackHomology_iff φ r).1 this
  · have hinst : (φ ≫ CommRingCat.ofHom (algebraMap Γ(T, V.1) p.ResidueField)).hom.toAlgebra =
        (inferInstance : Algebra c.R p.ResidueField) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have := hfib V p
    rwa [hinst] at this


/-- One direction of `isUniversallyFreeBottom_comp_iff`: a morphism universally of bottom rank
`r` after composing with the chart pulls the dual cokernel sheaf back to a finite locally free
module of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_pullback_dualCoker_of_isUniversallyFreeBottom
    {T : Scheme.{u}} (t : T ⟶ Spec c.R) (r : ℕ) (hF : IsUniversallyFreeBottom E a r (t ≫ c.ι)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback t).obj c.dualCoker) r := by
  refine c.isFiniteLocallyFreeOfRank_pullback_dualCoker_of_forall_affineOpens t r
    (fun V _ => (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ r).2 (hF _ V.2.fromSpec))
    fun V p _ => ?_
  set φ := Spec.preimage (V.2.fromSpec ≫ t)
  let ψ : Γ(T, V.1) ⟶ CommRingCat.of p.ResidueField :=
    CommRingCat.ofHom (algebraMap Γ(T, V.1) p.ResidueField)
  have hmor : Spec.map (φ ≫ ψ) ≫ c.ι = (Spec.map ψ ≫ V.2.fromSpec) ≫ t ≫ c.ι := by
    rw [Spec.map_comp, Spec.map_preimage]
    simp only [Category.assoc]
  have := hF _ (Spec.map ψ ≫ V.2.fromSpec)
  rw [← hmor, ← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at this
  exact (Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq
    ((c.isFiniteLocallyFreeOfRank_pullbackHomology_iff (φ ≫ ψ) r).1 this)).2.le

/-- One direction of `isUniversallyFreeBottom_comp_iff`: a morphism along which the dual cokernel
sheaf pulls back to a finite locally free module of rank `r` is universally of bottom rank `r`
after composing with the chart. -/
private theorem isUniversallyFreeBottom_comp_of_isFiniteLocallyFreeOfRank {T : Scheme.{u}}
    (t : T ⟶ Spec c.R) (r : ℕ) (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback t).obj c.dualCoker) r) :
    IsUniversallyFreeBottom E a r (t ≫ c.ι) := by
  intro Y' g
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  refine isFiniteLocallyFreeOfRank_of_forall_affineOpens _ r fun V => ?_
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  refine Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    (pullbackHomologyRestrictIso E a V.2.fromSpec (g ≫ t ≫ c.ι)) ?_
  set φ := Spec.preimage ((V.2.fromSpec ≫ g) ≫ t)
  have hmor : V.2.fromSpec ≫ g ≫ t ≫ c.ι = Spec.map φ ≫ c.ι := by
    rw [Spec.map_preimage]
    simp only [Category.assoc]
  rw [hmor, c.isFiniteLocallyFreeOfRank_pullbackHomology_iff φ r]
  let := φ.hom.toAlgebra
  refine LinearMap.isFiniteLocallyFreeOfRank_ker_baseChange _ c.d.hom ?_
  rw [← c.isFiniteLocallyFreeOfRank_pullback_dualCoker_iff φ r]
  have hpb : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (V.2.fromSpec ≫ g)).obj
        ((Scheme.Modules.pullback t).obj c.dualCoker)) r :=
    Grassmannian.isFiniteLocallyFreeOfRank_pullback (V.2.fromSpec ≫ g).base
      (V.2.fromSpec ≫ g).toRingCatSheafHom _ r h
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at hpb
  exact hpb.of_iso (c.pullbackDualCokerIso (V.2.fromSpec ≫ g) t)

/-- **The universal bottom rank condition on a chart is local freeness of the pulled back dual
cokernel.** A morphism `t : T ⟶ Spec R` into a chart is universally of bottom rank `r` after
composing with the chart exactly when the pullback along `t` of the dual cokernel sheaf is
finite locally free of rank `r`.

Both conditions are local on `T`, so it suffices to compare them on affine opens `Spec S` of
`T`. There the bottom cohomology is the kernel of the base changed bottom differential
(`pullbackHomologyIso`) and the pulled back dual cokernel sheaf is the base changed dual
cokernel; `LinearMap.isFiniteLocallyFreeOfRank_baseChange_dualCoker` and
`LinearMap.isFiniteLocallyFreeOfRank_ker_baseChange` compare the two, the fibre bound needed by
the first coming from the residue fields of `S`. -/
theorem isUniversallyFreeBottom_comp_iff {T : Scheme.{u}} (t : T ⟶ Spec c.R) (r : ℕ) :
    IsUniversallyFreeBottom E a r (t ≫ c.ι) ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback t).obj c.dualCoker) r :=
  ⟨c.isFiniteLocallyFreeOfRank_pullback_dualCoker_of_isUniversallyFreeBottom t r,
    c.isUniversallyFreeBottom_comp_of_isFiniteLocallyFreeOfRank t r⟩

end Chart

/-! ### The derived-fibre Betti number on a chart -/

/-- **Generation by `s` sections near a point is a bound on the fibre dimension.** A finite type
quasi-coherent module is generated by `s` sections near `y` exactly when the global sections of
its pullback to `Spec κ(y)` have dimension at most `s`. -/
theorem isGeneratedByNear_iff_finrank_pullback_residueField_le {T : Scheme.{u}} (F : T.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : ℕ) (y : T) :
    IsGeneratedByNear F s y ↔
      Module.finrank (T.residueField y)
        ((moduleSpecΓFunctor (R := T.residueField y)).obj
          ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F)) ≤ s := by
  obtain ⟨t⟩ : Nonempty ↑(Spec (T.residueField y)) := inferInstance
  have hfin : ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (T.fromSpecResidueField y).toLRSHom.toShHom F
  have hqc : ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ T.toRingedSpace
      (T.fromSpecResidueField y).toLRSHom.toShHom F ‹F.IsQuasicoherent›
  have hspec :
      IsGeneratedByNear ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F) s t ↔
        Module.finrank (T.residueField y)
          ((moduleSpecΓFunctor (R := T.residueField y)).obj
            ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F)) ≤ s := by
    rw [show t = IsLocalRing.closedPoint (ToType (T.residueField y)) from Subsingleton.elim _ _]
    exact AlgebraicGeometry.isGeneratedByNear_specField_iff_finrank_le
      (K := ToType (T.residueField y))
      ((Scheme.Modules.pullback (T.fromSpecResidueField y)).obj F) s
  have hpull := isGeneratedByNear_pullback_iff (T.fromSpecResidueField y) F s t
  rw [Scheme.fromSpecResidueField_apply] at hpull
  exact hpull.symm.trans hspec

namespace Chart

variable {E : DerivedCategory X.Modules} {a : ℤ} (c : Chart E a)

/-- Global sections of the pullback of the dual cokernel sheaf along `Spec S ⟶ Spec R`. -/
def moduleSpecΓPullbackDualCokerIso {S : CommRingCat.{u}} (g : Spec S ⟶ Spec c.R) :
    (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback g).obj c.dualCoker) ≅
      (ModuleCat.extendScalars.{u, u, u} (Spec.preimage g).hom).obj c.dualCokerModule :=
  (moduleSpecΓFunctor (R := S)).mapIso
      ((Scheme.Modules.pullbackCongr (Spec.map_preimage g).symm).app c.dualCoker ≪≫
        (pullbackTildeIso c.R S (Spec.preimage g)).app c.dualCokerModule) ≪≫
    ((tilde.toTildeΓNatIso (R := S)).app _).symm

/-- Global sections of the bottom cohomology at the point `Spec S ⟶ Spec R ⟶ X`. -/
def moduleSpecΓPullbackHomologyIso {S : CommRingCat.{u}} (g : Spec S ⟶ Spec c.R) :
    (moduleSpecΓFunctor (R := S)).obj (pullbackHomology E a (g ≫ c.ι)) ≅
      c.kernel (Spec.preimage g) :=
  (moduleSpecΓFunctor (R := S)).mapIso
      (eqToIso (congrArg (fun k => pullbackHomology E a (k ≫ c.ι)) (Spec.map_preimage g).symm) ≪≫
        c.pullbackHomologyIso (Spec.preimage g)) ≪≫
    ((tilde.toTildeΓNatIso (R := S)).app _).symm

/-- **On a chart, the derived-fibre Betti number in degree `a` is the dimension of the fibre of
the dual cokernel sheaf.** -/
theorem isGeneratedByNear_dualCoker_iff
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (s : ℕ)
    (y : Spec c.R) :
    IsGeneratedByNear c.dualCoker s y ↔
      DerivedFibreBetti.derivedFiberBetti X E hPC a (c.ι.base y) ≤ s := by
  set K := (Spec c.R).residueField y
  set g := (Spec c.R).fromSpecResidueField y
  have hb : DerivedFibreBetti.derivedFiberBetti (Spec c.R)
      ((derivedPullback c.ι.toLRSHom.toShHom).obj E)
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback c.ι E hPC) a y =
      Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        (pullbackHomology ((derivedPullback c.ι.toLRSHom.toShHom).obj E) a g)) := rfl
  rw [isGeneratedByNear_iff_finrank_pullback_residueField_le,
    (c.moduleSpecΓPullbackDualCokerIso g).toLinearEquiv.finrank_eq,
    ← derivedFiberBetti_derivedPullback_apply c.ι E hPC a y, hb,
    ((moduleSpecΓFunctor (R := K)).mapIso
      (pullbackHomologyCompIso E a g c.ι)).toLinearEquiv.finrank_eq,
    (c.moduleSpecΓPullbackHomologyIso g).toLinearEquiv.finrank_eq]
  let := (Spec.preimage g).hom.toAlgebra
  exact Iff.of_eq (congrArg (· ≤ s) (LinearMap.finrank_ker_baseChange_eq K c.d.hom).symm)

/-- **Under the Betti bound, local freeness of the bottom cohomology alone forces local freeness
of the pulled back dual cokernel.** If the dual cokernel sheaf is generated by `r` sections near
every point, a morphism `t : T ⟶ Spec R` along which `H^a(L(t ≫ ι)^* E)` is finite locally free of
rank `r` pulls the dual cokernel sheaf back to a finite locally free module of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_pullback_dualCoker_of_isGeneratedByNear {T : Scheme.{u}}
    (t : T ⟶ Spec c.R) (r : ℕ) (hgen : ∀ y : Spec c.R, IsGeneratedByNear c.dualCoker r y)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHomology E a (t ≫ c.ι)) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback t).obj c.dualCoker) r := by
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at h
  refine c.isFiniteLocallyFreeOfRank_pullback_dualCoker_of_forall_affineOpens t r
    (fun V _ => (h.restrict V.2.fromSpec).of_iso
      (pullbackHomologyRestrictIso E a V.2.fromSpec _).symm) fun V p _ => ?_
  set φ := Spec.preimage (V.2.fromSpec ≫ t)
  let ψ : Γ(T, V.1) ⟶ CommRingCat.of p.ResidueField :=
    CommRingCat.ofHom (algebraMap Γ(T, V.1) p.ResidueField)
  let pt : Spec (CommRingCat.of p.ResidueField) := IsLocalRing.closedPoint p.ResidueField
  have hf' : Module.finrank p.ResidueField
      ((moduleSpecΓFunctor (R := CommRingCat.of p.ResidueField)).obj
        ((Scheme.Modules.pullback (Spec.map (φ ≫ ψ))).obj c.dualCoker)) ≤ r :=
    (AlgebraicGeometry.isGeneratedByNear_specField_iff_finrank_le (K := p.ResidueField)
      ((Scheme.Modules.pullback (Spec.map (φ ≫ ψ))).obj c.dualCoker) r).1
      ((isGeneratedByNear_pullback_iff (Spec.map (φ ≫ ψ)) c.dualCoker r pt).2 (hgen _))
  rw [(c.moduleSpecΓPullbackDualCokerIso (Spec.map (φ ≫ ψ))).toLinearEquiv.finrank_eq,
    Spec.preimage_map] at hf'
  let := (φ ≫ ψ).hom.toAlgebra
  rwa [LinearMap.finrank_ker_baseChange_eq]

end Chart

end AlgebraicGeometry.BottomRankStratum

end
