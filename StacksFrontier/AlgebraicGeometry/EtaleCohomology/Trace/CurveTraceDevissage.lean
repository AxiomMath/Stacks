module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroCover

/-!
# The curve dévissage of the trace formula: reduction to its core

Let `k` be a finite field, `k̄` an algebraically closed extension of `k` and `Λ` a finite ring.
The proof of [Stacks, Tag 03UG] reduces the trace formula `T''(X, K) = T'(X, K)` on a curve `X`
over `k` to its **core** (end of Step 3): for a finite locally constant sheaf `F` of `Λ`-modules
with finite projective values on a smooth irreducible affine curve `U` over `k` with
`U(k) = ∅`, `T''(U, F) = Tr(π_U^* | RΓ_c(U_k̄, F)) = 0` (and `RΓ_c(U_k̄, F)` is perfect).
`Stacks.EtaleCohomology.CurveTraceCore` is that statement, for every such `U`, every
compactification of `U` and every such `F`.

This file carries out the part of the dévissage which takes place on the good open part of the
curve: the passage from a smooth curve without rational points which is a finite disjoint union
of affine irreducible curves to its connected components, through the decomposition
`0 → j_{A!} j_A^{-1} K → K → i_{B*} i_B^{-1} K → 0` attached to a decomposition into open and
closed parts `A ⊔ B` (Step 1 of Tag 03UG), the identification `i_{B*} = j_{B!}` for the open and
closed `B`, and the identification `RΓ_c(A_k̄, -) = RΓ_c(U_k̄, j_{A!} -)` along the induced
compactification.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main definitions

* `Stacks.EtaleCohomology.CurveTraceCore`: the core of the proof of Tag 03UG.
* `Stacks.EtaleCohomology.CompactSupportTraceVanishes`: `RΓ_c(X_k̄, K)` is perfect and the
  trace of `π_X^*` on it vanishes.

## Main results

* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_isCompl`: the vanishing for `K` on `W`
  follows from the vanishing for its restrictions to the two parts of a decomposition of `W` into
  complementary open (and closed) subschemes.
* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_partition`: the vanishing on a scheme
  partitioned into finitely many open subschemes follows from the vanishing on the pieces.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 and 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **The core of the proof of [Stacks, Tag 03UG]** (end of Step 3), for a finite ring `Λ` with
`#Λ` invertible in the finite field `k`: for every smooth connected affine curve `U` over `k`
without `k`-rational points, every compactification of `U` and every locally constant sheaf `F`
of `Λ`-modules on `U_étale` with finite projective values, `RΓ_c(U_k̄, F)` is perfect and
`Tr(π_U^* | RΓ_c(U_k̄, F)) = 0`. -/
def CurveTraceCore (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
    (_hΛ : (Nat.card Λ : k) ≠ 0) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
    (hcard : Fintype.card k = p ^ q) : Prop :=
  ∀ (U : Scheme.{u}) (fU : U ⟶ Spec (.of k)) [IsCurve k fU] [Smooth fU] [LocallyOfFiniteType fU]
    [QuasiCompact fU] [IsSeparated fU] [ConnectedSpace U] [IsAffine U]
    [IsEmpty (rationalPoints fU)] (J : CompactificationOf (Over.mk fU))
    (F : EtaleModules.{u, 0} Λ U),
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology F →
      ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} Λ fU J kbar
            ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)),
        perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ fU J kbar p q hcard
            ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) =
          0

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- `RΓ_c(X_k̄, K)` is perfect and `Tr(π_X^* | RΓ_c(X_k̄, K)) = 0`, for the compactification `J`
of `X`. -/
def CompactSupportTraceVanishes {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (J : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    Prop :=
  ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K)),
    perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard K)) = 0

variable {Λ kbar p q hcard}

/-- The vanishing only depends on the complex up to isomorphism. -/
theorem CompactSupportTraceVanishes.of_iso {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    {J : CompactificationOf (Over.mk f)} {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    (e : K ≅ K') (h : CompactSupportTraceVanishes Λ kbar p q hcard f J K) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J K' := by
  obtain ⟨hp, ht⟩ := h
  have hp' := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ f J kbar e hp
  exact ⟨hp', (perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso Λ f J kbar p q
    hcard e hp hp').symm.trans ht⟩

/-- **The vanishing on an open subscheme for the induced compactification gives the vanishing for
the extension by zero**: `RΓ_c(U_k̄, K) ≅ RΓ_c(X_k̄, j_{U!} K)`, Frobenius-equivariantly. -/
theorem CompactSupportTraceVanishes.extensionByZero {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    {J : CompactificationOf (Over.mk f)} {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    {K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)}
    (h : CompactSupportTraceVanishes Λ kbar p q hcard (jU ≫ f) (J.restrictOpen jU) K) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J
      ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K) := by
  obtain ⟨hp, ht⟩ := h
  let e := DerivedCategory.Plus.ι.mapIso
    (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f J jU kbar K)
  have hp' := StacksDraft.Perfect.isPerfect_of_iso e.symm hp
  refine ⟨hp', Eq.trans ?_ ht⟩
  refine (perfectDerivedTrace_congr Λ ⟨_, hp⟩ ⟨_, hp'⟩ e _ _ ?_).symm
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Plus.ι.map
    (compactSupportFrobeniusCohomologyRestrictOpenIso_hom_frobenius Λ f J jU kbar p q hcard K)

/-- **`j_! ≅ j_*` for an open immersion which is also a closed immersion**: the square of `𝟙`,
`𝟙`, `j`, `j` is cartesian since `j` is a monomorphism. -/
def etaleModuleExtensionByZeroIsoDirectImageOfIsClosedImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    etaleModuleExtensionByZero.{u, 0} Λ j ≅ etaleModuleDirectImage.{u, 0} Λ j :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 U)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (etaleModuleInverseImageIdIso Λ U).symm)).symm _ ≪≫
    etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ (𝟙 U) (𝟙 U) j j
      (IsKernelPair.id_of_mono j) ≪≫
    Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso Λ U) _ ≪≫ Functor.leftUnitor _

variable [Finite Λ]

/-- **The vanishing along a decomposition into complementary open subschemes.** If `W = A ⊔ B`
with `A`, `B` open, and the trace vanishes on `RΓ_c(A_k̄, K|_A)` and on `RΓ_c(B_k̄, K|_B)` for the
induced compactifications, it vanishes on `RΓ_c(W_k̄, K)`: by Step 1 of Tag 03UG along
`0 → j_{A!} K|_A → K → i_{B*} K|_B → 0`, with `i_{B*} = j_{B!}` since `B` is also closed. -/
theorem compactSupportTraceVanishes_of_isCompl {W : Scheme.{u}} (g : W ⟶ Spec (.of k))
    (J : CompactificationOf (Over.mk g)) (A B : W.Opens) (hAB : IsCompl A B)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ W))
    (hA : CompactSupportTraceVanishes Λ kbar p q hcard (A.ι ≫ g) (J.restrictOpen A.ι)
      ((etaleModuleRestriction.{u, 0} Λ A.ι).mapCochainComplexPlus.obj K))
    (hB : CompactSupportTraceVanishes Λ kbar p q hcard (B.ι ≫ g) (J.restrictOpen B.ι)
      ((etaleModuleRestriction.{u, 0} Λ B.ι).mapCochainComplexPlus.obj K)) :
    CompactSupportTraceVanishes Λ kbar p q hcard g J K := by
  have h1 : (A : Set W) ∩ B = ∅ := by
    rw [← TopologicalSpace.Opens.coe_inf, hAB.inf_eq_bot, TopologicalSpace.Opens.coe_bot]
  have h2 : (A : Set W) ∪ B = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, hAB.sup_eq_top, TopologicalSpace.Opens.coe_top]
  have hcompl : (B : Set W) = (A : Set W)ᶜ :=
    (IsCompl.of_eq (x := (A : Set W)) (y := B) h1 h2).symm.eq_compl
  have : IsClosedImmersion B.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hcompl]
    exact A.isOpen.isClosed_compl)
  have hij : Set.range A.ι.base = (Set.range B.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, hcompl, compl_compl]
  have hS := openClosedCochainShortComplex_shortExact Λ B.ι A.ι hij K.obj
  obtain ⟨hp₁, ht₁⟩ := hA.extensionByZero A.ι
  let N : etaleModuleRestriction.{u, 0} Λ B.ι ⋙ etaleModuleExtensionByZero.{u, 0} Λ B.ι ≅
      etaleModuleInverseImage.{u, 0} Λ B.ι ⋙ etaleModuleDirectImage.{u, 0} Λ B.ι :=
    Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ B.ι).symm _ ≪≫
      Functor.isoWhiskerLeft _ (etaleModuleExtensionByZeroIsoDirectImageOfIsClosedImmersion B.ι)
  let e₃ : (etaleModuleExtensionByZero.{u, 0} Λ B.ι).mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ B.ι).mapCochainComplexPlus.obj K) ≅
      (etaleModuleDirectImage.{u, 0} Λ B.ι).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ B.ι).mapCochainComplexPlus.obj K) :=
    ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents (fun n => N.app (K.obj.X n))
      (fun a b _ => (N.hom.naturality (K.obj.d a b)).symm))
  obtain ⟨hp₃, ht₃⟩ := (hB.extensionByZero B.ι).of_iso e₃
  have h₁ := ((etaleModuleExtensionByZero.{u, 0} Λ A.ι).mapCochainComplexPlus.obj
    ((etaleModuleRestriction.{u, 0} Λ A.ι).mapCochainComplexPlus.obj K)).property
  have h₃ := ((etaleModuleDirectImage.{u, 0} Λ B.ι).mapCochainComplexPlus.obj
    ((etaleModuleInverseImage.{u, 0} Λ B.ι).mapCochainComplexPlus.obj K)).property
  have hp₂ := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ g J kbar hS h₁ K.property h₃
    hp₁ hp₃
  refine ⟨hp₂, ?_⟩
  have := canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ g J kbar p q hcard hS h₁ K.property
    h₃ hp₁ hp₂ hp₃
  simp only [canonicalCompactSupportLefschetzNumber, globalLefschetzNumber,
    canonicalFrobeniusActionOnCompactSupport] at this
  exact this.trans ((congrArg₂ (· + ·) ht₁ ht₃).trans (add_zero 0))

/-- Restriction along a composite of étale morphisms, degreewise on a bounded below complex:
`(a ≫ b)^{-1} K ≅ a^{-1} (b^{-1} K)`. -/
def restrictionCompPlusIso {T V X : Scheme.{u}} (a : T ⟶ V) (b : V ⟶ X) [Etale a] [Etale b]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleRestriction.{u, 0} Λ (a ≫ b)).mapCochainComplexPlus.obj K ≅
      (etaleModuleRestriction.{u, 0} Λ a).mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ b).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
    (fun n => (etaleModuleRestrictionCompIso.{u, 0} Λ a b).symm.app (K.obj.X n))
    (fun _ _ _ => ((etaleModuleRestrictionCompIso.{u, 0} Λ a b).inv.naturality _).symm))

/-- **The vanishing on a finite union of disjoint open pieces.** Let `Z i` be pairwise disjoint
opens of `X`, and suppose that the trace vanishes on `RΓ_c(V_k̄, K|_V)` for every open subscheme
`V ⟶ X` whose image is one of the `Z i` and every compactification of `V`. Then it vanishes for
every open subscheme whose image is the union of finitely many (at least one) of the `Z i`. -/
theorem compactSupportTraceVanishes_of_partition {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    {ι : Type*} (Z : ι → X.Opens) (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hleaf : ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e] (i : ι),
      Set.range e.base = Z i → ∀ (g : V ⟶ Spec (.of k)), g = e ≫ fX →
        ∀ J : CompactificationOf (Over.mk g), CompactSupportTraceVanishes Λ kbar p q hcard g J
          ((etaleModuleRestriction.{u, 0} Λ e).mapCochainComplexPlus.obj K))
    (s : Finset ι) (hs : s.Nonempty) :
    ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e],
      Set.range e.base = ⋃ i ∈ s, (Z i : Set X) → ∀ (g : V ⟶ Spec (.of k)), g = e ≫ fX →
        ∀ J : CompactificationOf (Over.mk g), CompactSupportTraceVanishes Λ kbar p q hcard g J
          ((etaleModuleRestriction.{u, 0} Λ e).mapCochainComplexPlus.obj K) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro V e _ he g hg J
    refine hleaf V e a ?_ g hg J
    rw [he]
    ext x
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  | cons a s ha hs ih =>
    intro V e _ he g hg J
    let A : V.Opens := ⟨e ⁻¹' (Z a : Set X), (Z a).isOpen.preimage e.continuous⟩
    let B : V.Opens := ⟨e ⁻¹' (⋃ i ∈ s, (Z i : Set X)),
      (isOpen_biUnion fun i _ => (Z i).isOpen).preimage e.continuous⟩
    have hBs : (B : Set V) = e ⁻¹' (⋃ i ∈ s, (Z i : Set X)) := rfl
    have hAB : IsCompl A B := by
      constructor
      · rw [← TopologicalSpace.Opens.coe_disjoint, hBs]
        exact Disjoint.preimage e (Set.disjoint_iUnion₂_right.2 fun i hi =>
          TopologicalSpace.Opens.coe_disjoint.2 (hdisj fun h => ha (h ▸ hi)))
      · rw [codisjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_sup,
          TopologicalSpace.Opens.coe_top, hBs, Set.eq_univ_iff_forall]
        intro v
        obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 (he.subset (Set.mem_range_self v))
        rcases Finset.mem_cons.1 hi with rfl | hi
        exacts [Or.inl hvi, Or.inr (Set.mem_preimage.2 (Set.mem_iUnion₂.2 ⟨i, hi, hvi⟩))]
    refine compactSupportTraceVanishes_of_isCompl g J A B hAB _ ?_ ?_
    · refine CompactSupportTraceVanishes.of_iso (restrictionCompPlusIso A.ι e K) ?_
      refine hleaf A.toScheme (A.ι ≫ e) a ?_ (A.ι ≫ g) (by rw [hg, Category.assoc])
        (J.restrictOpen A.ι)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      show (⇑e) '' ((⇑e) ⁻¹' (Z a : Set X)) = _
      rw [Set.image_preimage_eq_inter_range]
      refine Set.inter_eq_left.2 ?_
      rw [he]
      exact Set.subset_biUnion_of_mem (u := fun i => (Z i : Set X)) (Finset.mem_cons_self a s)
    · refine CompactSupportTraceVanishes.of_iso (restrictionCompPlusIso B.ι e K) ?_
      refine ih B.toScheme (B.ι ≫ e) ?_ (B.ι ≫ g) (by rw [hg, Category.assoc])
        (J.restrictOpen B.ι)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hBs,
        Set.image_preimage_eq_inter_range]
      refine Set.inter_eq_left.2 ?_
      rw [he]
      exact Set.biUnion_subset_biUnion_left (fun i hi => Finset.mem_cons_of_mem hi)

/-- **The core on an open piece.** Let `Z` be an open of `X` which is an integral affine curve,
smooth over `k`, without `k`-rational points, and on all of whose open subschemes `F` is locally
constant with finite projective values. Then `CurveTraceCore` gives the vanishing of the trace on
`RΓ_c(V_k̄, F|_V)` for every open subscheme `V ⟶ X` with image `Z` and every compactification of
`V`. -/
theorem compactSupportTraceVanishes_of_curveTraceCore [IsAlgClosed kbar] [CharP kbar p]
    [Algebra.IsAlgebraic k kbar]
    {hΛ : (Nat.card Λ : k) ≠ 0} (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [LocallyOfFiniteType fX] [IsSeparated fX] (Z : X.Opens)
    [IsIntegral Z] [IsAffine Z] (hZdim : topologicalKrullDim Z = 1) [Smooth (Z.ι ≫ fX)]
    (hZrat : IsEmpty (rationalPoints (Z.ι ≫ fX))) (F : EtaleModules.{u, 0} Λ X)
    (hF : ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e], Set.range e.base ⊆ Z →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ V.smallEtaleTopology
        ((etaleModuleRestriction.{u, 0} Λ e).obj F))
    (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e] (he : Set.range e.base = Z)
    (g : V ⟶ Spec (.of k)) (hg : g = e ≫ fX) (J : CompactificationOf (Over.mk g)) :
    CompactSupportTraceVanishes Λ kbar p q hcard g J
      ((etaleModuleRestriction.{u, 0} Λ e).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩) := by
  subst hg
  let φ := IsOpenImmersion.isoOfRangeEq e Z.ι (by rw [Scheme.Opens.range_ι, he])
  have hφ : φ.hom ≫ Z.ι = e := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : Nonempty V := ⟨φ.inv (Nonempty.some inferInstance)⟩
  have : IsIntegral V := isIntegral_of_isOpenImmersion φ.hom
  have : IsAffine V := IsAffine.of_isIso φ.hom
  have : Smooth (e ≫ fX) := by rw [← hφ, Category.assoc]; infer_instance
  have : IsSeparated e := IsSeparated.isSeparated_of_mono e
  have : QuasiCompact (e ≫ fX) := quasiCompact_of_compactSpace _
  have : IsCurve k (e ≫ fX) :=
    { topologicalKrullDim_eq_one :=
        (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso φ).isHomeomorph).trans hZdim }
  have : IsEmpty (rationalPoints (e ≫ fX)) := ⟨fun x => hZrat.false
    (rationalPointsMap (Z.ι ≫ fX) φ.hom (by rw [← Category.assoc, hφ]) x)⟩
  obtain ⟨hp, ht⟩ := hcore V (e ≫ fX) J ((etaleModuleRestriction.{u, 0} Λ e).obj F)
    (hF V e he.le)
  exact CompactSupportTraceVanishes.of_iso
    ((singlePlusFunctorCompMapCochainComplexPlusIso (etaleModuleRestriction.{u, 0} Λ e)).app F).symm
    ⟨hp, ht⟩

end Standard

end Stacks.EtaleCohomology

end
