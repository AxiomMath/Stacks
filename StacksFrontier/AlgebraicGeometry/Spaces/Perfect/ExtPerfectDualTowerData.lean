module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtCoefficientEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImageCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# The data of Stacks 08JR, part (B)

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` locally of finite type and quasi-separated,
`E ∈ D^-_{Coh}(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat over `Y`, with
support proper over `Y`.  Following the proof of Stacks 08JR (B), this file

* chooses a quasi-compact open neighbourhood `V` of the support of `𝒢^•` (a Noetherian algebraic
  space), with its elementary distinguished square;
* writes the restriction `E|_V`, pseudo-coherent by Stacks 08IK, as the target of a tower of
  perfect objects `tEₙ ⟶ E|_V` inducing isomorphisms on cohomology in degrees `≥ -(n + 1)`
  (the approximations of Stacks 08HP, as in the proof of Stacks 0DKB);
* forms the tower `Lₙ = (R(f|_V)_* RSheafHom(tEₙ, 𝒢^•|_V))^∨` of
  `AlgebraicGeometry.Space.extPerfectDualTower` and its pseudo-coherent homotopy colimit `L`,
  with `Ext^i(L, ℱ) = Ext^i(E|_V, 𝒢^•|_V ⊗ (f|_V)^*ℱ) = Ext^i(E, 𝒢^• ⊗ f^*ℱ)`, the last step
  being the restriction to `V` (Stacks 08GG).

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}


/-! ### The neighbourhood of the support -/

/-- **A quasi-compact open neighbourhood of the support of `𝒢^•`**, as in
`AlgebraicGeometry.Space.exists_isElementaryDistinguishedSquare_of_flatProperSupportComplex`,
recording also that `V` is an open subspace. -/
theorem exists_isOpenSubspace_isElementaryDistinguishedSquare_of_flatProperSupportComplex
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    ∃ (Z : Set (points B S hS X.1)) (hZ : IsClosed Z) (V : Subfunctor X.1)
      (_ : IsOpenSubspace B S hS V)
      (hsq : IsElementaryDistinguishedSquare B S hS X.2
        (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι),
      IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ ∧
      (∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z ∧
      Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  obtain ⟨V, hV, hVqc, hZV⟩ := exists_isQuasiCompactSpace_openSubspace_of_isCompact B S hS X.2 Z hZc
  refine ⟨Z, hZcl, V, hV,
    isElementaryDistinguishedSquare_openSubspaceOfPoints B S hS X.2 Z hZcl V hV hZV, hZp, hGZ,
    hVqc, ?_, hZV⟩
  rw [edsComplementPoints, range_pointsMap_ι_openSubspaceOfPoints, compl_compl]

/-- **The hypotheses of Stacks 0DKJ are invariant under termwise isomorphisms of complexes.** -/
theorem FlatProperSupportComplex.of_iso {f : X ⟶ Y} {hf : IsLocallyOfFiniteType B S hS f.hom}
    {G G' : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ} (e : ∀ q, G.X q ≅ G'.X q)
    (hG : FlatProperSupportComplex B S hS f hf G) : FlatProperSupportComplex B S hS f hf G' where
  bounded := by
    obtain ⟨a, b, h⟩ := hG.bounded
    exact ⟨a, b, fun q hq => (h q hq).of_iso (e q).symm⟩
  isCoherent q := isCoherent_of_iso B S hS X.2 (e q) (hG.isCoherent q)
  isFlatOver q := IsFlatOver.of_iso B S hS X.2 (e q) (hG.isFlatOver q)
  properSupport := by
    obtain ⟨Z, hZ, hp, hs⟩ := hG.properSupport
    exact ⟨Z, hZ, hp, fun q => (supportOfSheaf_eq_of_iso B S hS X (e q)).symm.le.trans (hs q)⟩

/-! ### A tower of perfect approximations (the proof of Stacks 0DKB) -/

section Approximations

variable (hTop : B.Contains (⊤_ Scheme.{u})) (Z : AlgebraicSpaces B S hS)
  (hqc : IsQuasiCompactSpace B S hS Z.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hTop Z.1)
  {K : smallEtaleModulesDerived B S hS Z} (hK : SmallEtaleIsPseudoCoherent B S hS K)

include hqc hqs hK in
/-- The first member of the tower: an approximation of `(|Z|, K, -2)` (Stacks 08HP). -/
theorem exists_isPerfect_approximation_smallEtale :
    ∃ (P : smallEtaleModulesDerived B S hS Z) (_ : SmallEtaleIsPerfect B S hS P) (β : P ⟶ K),
      ∀ i : ℤ, -1 ≤ i → IsIso ((smallEtaleModulesHomology B S hS Z i).map β) := by
  obtain ⟨P, hP, α, hαi, -⟩ :=
    exists_isPerfect_approximation_of_isPseudoCoherent B S hS hTop Z.1 Z.2 hqc hqs K hK (-2)
  exact ⟨P, hP, α, fun i hi => hαi i (by omega)⟩

include hqc hqs hK in
/-- The induction step of the tower: a map from a perfect object to `K` factors through a perfect
approximation of `(|Z|, K, -(n + 2))` (Stacks 08HP, as in the proof of Stacks 0DKB). -/
theorem exists_isPerfect_factorization_smallEtale {P : smallEtaleModulesDerived B S hS Z}
    (hP : SmallEtaleIsPerfect B S hS P) (β : P ⟶ K) (n : ℕ) :
    ∃ (Q : smallEtaleModulesDerived B S hS Z) (_ : SmallEtaleIsPerfect B S hS Q) (g : P ⟶ Q)
      (β' : Q ⟶ K), g ≫ β' = β ∧
        ∀ i : ℤ, -((n : ℤ) + 2) ≤ i → IsIso ((smallEtaleModulesHomology B S hS Z i).map β') := by
  obtain ⟨Q, g, β', hQ, hg, hβ⟩ :=
    exists_perfect_factorization B S hS hTop Z.1 Z.2 hqc hqs hK hP β (-((n : ℤ) + 2))
  exact ⟨Q, hQ, g, β', hg, hβ⟩

include hqc hqs hK in
/-- **A tower of perfect approximations** `tE₀ ⟶ tE₁ ⟶ ⋯ ⟶ K` of a pseudo-coherent `K` on a
quasi-compact and quasi-separated algebraic space, the `n`-th map inducing isomorphisms on
cohomology in degrees `> -(n + 2)` (the construction of the proof of Stacks 0DKB). -/
theorem exists_isPerfect_tower_smallEtale :
    ∃ (tE : ℕ ⥤ smallEtaleModulesDerived B S hS Z) (_ : ∀ n, SmallEtaleIsPerfect B S hS (tE.obj n))
      (cE : ∀ n, tE.obj n ⟶ K),
      (∀ n, tE.map (homOfLE (Nat.le_succ n)) ≫ cE (n + 1) = cE n) ∧
      ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
        IsIso ((smallEtaleModulesHomology B S hS Z j).map (cE n)) := by
  obtain ⟨P₀, hP₀, β₀, hβ₀⟩ := exists_isPerfect_approximation_smallEtale B S hS hTop Z hqc hqs hK
  choose Q hQ g β' hg hβ' using fun (n : ℕ) (P : smallEtaleModulesDerived B S hS Z)
    (hP : SmallEtaleIsPerfect B S hS P) (β : P ⟶ K) =>
      exists_isPerfect_factorization_smallEtale B S hS hTop Z hqc hqs hK hP β n
  let st : ℕ → {p : (Σ P : smallEtaleModulesDerived B S hS Z, P ⟶ K) //
      SmallEtaleIsPerfect B S hS p.1} :=
    fun n => Nat.rec ⟨⟨P₀, β₀⟩, hP₀⟩ (fun n s => ⟨⟨Q n s.1.1 s.2 s.1.2, β' n s.1.1 s.2 s.1.2⟩,
      hQ n s.1.1 s.2 s.1.2⟩) n
  let tE : ℕ ⥤ smallEtaleModulesDerived B S hS Z :=
    Functor.ofSequence (X := fun n => (st n).1.1) (fun n => g n (st n).1.1 (st n).2 (st n).1.2)
  refine ⟨tE, fun n => (st n).2, fun n => (st n).1.2, fun n => ?_, fun n j hj => ?_⟩
  · rw [Functor.ofSequence_map_homOfLE_succ]
    exact hg n (st n).1.1 (st n).2 (st n).1.2
  · cases n with
    | zero => exact hβ₀ j (by omega)
    | succ n => exact hβ' n (st n).1.1 (st n).2 (st n).1.2 j (by push_cast at hj; omega)

end Approximations

/-! ### The comparison of coefficients of Stacks 0A1M -/

/-- The boundary-map compatibility of `AlgebraicGeometry.Space.tensorPullbackComplexNatTrans`
(Stacks 0A1M), in the form taken by
`AlgebraicGeometry.Space.exists_isPseudoCoherent_extPerfectDual_of_coefficient`. -/
theorem tensorPullbackComplexNatTrans_singleδ (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) :
    (extPerfectCoefficientFunctor B S hS f G).map hT.singleδ ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (smallEtaleModulesSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G
          (tensorPullbackComplexNatTrans f G) T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G (tensorPullbackComplexNatTrans f G) T.X₃ ≫
        extPerfectCoefficientDelta B S hS f G T
          (shortExact_tensorPullbackComplex_map_single hG hT) :=
  tensorPullbackComplexNatTrans_triangleOfSESδ hG hT

/-! ### The neighbourhood `V` -/

section Neighbourhood

variable (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hG : SmallEtaleFlatProperSupport B S hS f hf G)
  {Z : Set (points B S hS X.1)} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)

include hTop hf hfqs hY in
/-- The neighbourhood `V` is Noetherian. -/
theorem isNoetherian_edsEtale_openSubspaceOfPoints (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) :
    IsNoetherian B S hS hTop (edsEtale B S hS hsq).1 :=
  isNoetherian_edsEtale_of_isQuasiCompactSpace B S hS hsq hTop f hf hfqs hY hVqc

/-- The restriction `𝒢^•|_V` of `𝒢^•`, in the spelling of
`AlgebraicGeometry.Space.pullbackComplexSmallEtale`. -/
abbrev edsRestrictComplex :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (edsEtale B S hS hsq))) ℤ :=
  (pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G

include hTop hf hfqs hY hG in
/-- **`𝒢^•|_V` satisfies the hypotheses of Stacks 0DKJ for `V ⟶ Y`.** -/
theorem flatProperSupport_edsRestrictComplex (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z)
    (hZp : ∀ hZ : IsClosed Z, IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ) :
    SmallEtaleFlatProperSupport B S hS (edsEtaleHom B S hS hsq ≫ f)
      (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
        (edsRestrictComplex B S hS G hsq) := by
  have hN := isNoetherian_edsEtale_openSubspaceOfPoints B S hS hTop f hf hfqs hY hsq hVqc
  have hT : IsProperOver B S hS X.2 Y.2 f.hom hf
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ)) hsq.isClosedComplement := by
    simpa only [hcompl] using hZp (hcompl ▸ hsq.isClosedComplement)
  exact FlatProperSupportComplex.of_iso B S hS
    (fun q => (etaleModulePullbackIsoPullbackModules B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).app (G.X q))
    (flatProperSupportComplex_edsEtaleRestrict B S hS hsq f hf hN.2.2 G hG
      (fun q => (hGZ q).trans hcompl.symm.le) hT)

end Neighbourhood


/-- The maps of a short complex of modules placed in degree `0` compose to zero. -/
theorem single_map_comp_map_eq_zero (T : ShortComplex (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS Y))) :
    (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).map T.f ≫ (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.g = 0 := by
  rw [← Functor.map_comp, T.zero, Functor.map_zero]

/-! ### Restriction to `V` on `Ext` -/

section Restriction

variable {Z : Set (points B S hS X.1)} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
  (f : X ⟶ Y) (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))

/-- If the supports of the terms of `𝒢^•` lie in the complement of `X ∖ Z`, then for every
module `ℱ` on `Y` the cohomology of `𝒢^• ⊗ f^*ℱ` is supported there. -/
theorem cohomologySupportedOn_tensorPullbackSingleDerived
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆
      edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ))
        (F : Modules.{u, u} B S hS Y.1 Y.2) :
    CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS
      (openSubspaceOfPoints B S hS X.1 Zᶜ))
      (tensorPullbackComplexDerived f G ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)) :=
  cohomologySupportedOn_Q_obj_tensorPullbackComplex_single f G _ hGZ F

/-- Composing `x` with the map induced by `q : ℱ ⟶ ℱ'` on `𝒢^•|_V ⊗ f|_V^*(-)`, read in the two
spellings of `D(𝒪_V)`. -/
theorem comp_extPerfectCoefficientModulesFunctor_map_eq {F F' : Modules.{u, u} B S hS Y.1 Y.2}
    (q : F ⟶ F') (i : ℤ)
    (x : ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq)) ⟶
        ((extPerfectCoefficientModulesFunctor B S hS (edsEtaleHom B S hS hsq ≫ f)
          (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).obj F)⟦i⟧) :
    (x ≫ ((extPerfectCoefficientModulesFunctor B S hS (edsEtaleHom B S hS hsq ≫ f)
          (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map q)⟦i⟧' :
        ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ _) =
      ((x : (edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F))⟦i⟧) ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
            (ComplexShape.up ℤ) 0).map q)))⟦i⟧' :) :=
  rfl


/-- The boundary map of `𝒢^•|_V ⊗ f|_V^*(-)` of a short exact sequence, composed after `x`, read in
the two spellings of `D(𝒪_V)`. -/
theorem comp_extPerfectCoefficientModulesDelta_eq
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).ShortExact)
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact) (i : ℤ)
    (x : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq))
        ((extPerfectCoefficientModulesFunctor B S hS (edsEtaleHom B S hS hsq ≫ f)
          (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).obj T.X₃) i) :
    (x.comp (extPerfectCoefficientModulesDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
        (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) hex T hT) (add_comm 1 i) :
      ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
        (edsEtale B S hS hsq)) ⟶ _) =
      (ShiftedHom.comp (C := DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2)) (X := (edsEtaleRestrict B S hS hsq).obj E)
        (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
            (ComplexShape.up ℤ) 0).obj T.X₃)) x
        (DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
            ℤ) 0).map T.f) ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
            ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
          (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
              (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))))
          (hex T hT)) (add_comm 1 i) :) :=
  rfl

end Restriction


section Transport

variable {Z : Set (points B S hS X.1)} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
  (f : X ⟶ Y) (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (Linf : DerivedCategory
      (Modules.{u, u} B S hS Y.1 Y.2))

/-- **`Ext^i_Y(L, ℱ) ≃+ Ext^i_V(E|_V, …) ≃+ Ext^i_X(E, 𝒢^• ⊗ f^*ℱ)` is natural in `ℱ`.** -/
theorem edsRestricted_naturality (hN : ∀ F : Modules.{u, u} B S hS Y.1 Y.2, CohomologySupportedOn
    B S hS X.1 X.2
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ))
      (tensorPullbackComplexDerived f G ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)))
        (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
        (((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ ((extPerfectCoefficientModulesFunctor B S hS
          (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
          (edsEtaleHom B S hS hsq)).obj G)).obj F)⟦i⟧))
    (hnat : ∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
          Φ F hF i e ≫ ((extPerfectCoefficientModulesFunctor B S hS (edsEtaleHom B S hS hsq ≫ f)
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map q)⟦i⟧')
    {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
      (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F')
    (i : ℤ) (e : Linf ⟶ ((DerivedCategory.singleFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) :
    ((Φ F' hF' i).trans (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F') (hN F') i).symm) (e ≫ ((DerivedCategory.singleFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
      ((Φ F hF i).trans (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F) (hN F) i).symm) e ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex f G).map ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).map q)))⟦i⟧' :=
  (congrArg (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
      ℤ) 0).obj F') (hN F') i).symm
      ((hnat hF hF' q i e).trans (comp_extPerfectCoefficientModulesFunctor_map_eq B S hS hsq f G E
        q i (Φ F hF i e)))).trans
    (edsRestrictCoefficientShiftedExt_symm_naturality hsq f G E (hN F) (hN F')
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).map q) i (Φ F hF i e))

/-- If `Φ` carries the boundary of a short exact sequence `T` to composition with the boundary
map of `𝒢^•|_V ⊗ f|_V^*(-)`, then it carries it to composition with the boundary of the
triangle of `𝒢^•|_V ⊗ f|_V^*T` in `D(𝒪_V)`. -/
theorem edsRestricted_delta_aux (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2)
    (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
        (((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ ((extPerfectCoefficientModulesFunctor B S hS
          (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
          (edsEtaleHom B S hS hsq)).obj G)).obj F)⟦i⟧)) (hex : ∀ T : ShortComplex
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)), T.ShortExact →
          ((T.map (HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G))).ShortExact)
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
    (e : ShiftedHom Linf ((DerivedCategory.singleFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i)
    (hδT : Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (show ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
            (edsEtale B S hS hsq)) ((extPerfectCoefficientModulesFunctor B S hS
            (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
            (edsEtaleHom B S hS hsq)).obj G)).obj T.X₃) i from Φ T.X₃ h₃ i e).comp
            (extPerfectCoefficientModulesDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) hex T hT)
              (add_comm 1 i)) :
    Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
      (ShiftedHom.comp (C := DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2)) (X := (edsEtaleRestrict B S hS hsq).obj E)
        (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
            (edsEtaleHom B S hS hsq)).obj G) ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj T.X₃)) (Φ
            T.X₃ h₃ i e)
        (DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
            ℤ) 0).map T.f) ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
            ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex
            (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
            (edsEtaleHom B S hS hsq)).obj G))) (hex T hT)) (add_comm 1 i) :) :=
  hδT.trans (comp_extPerfectCoefficientModulesDelta_eq B S hS hsq f G E hex T hT i (Φ T.X₃ h₃ i e))

/-- The restriction step of `AlgebraicGeometry.Space.edsRestricted_delta`. -/
theorem edsRestricted_delta_restrict (hN : ∀ F : Modules.{u, u} B S hS Y.1 Y.2,
    CohomologySupportedOn B S hS X.1 X.2
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ))
      (tensorPullbackComplexDerived f G ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)))
        (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
        T.ShortExact → ((T.map (HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (hexX : ∀ T : ShortComplex
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)), T.ShortExact →
        ((T.map (HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex f G)).ShortExact)
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact) (i : ℤ)
    (x : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E)
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G) ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj T.X₃)) i) :
    (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj T.X₁)
      (hN T.X₁) (i + 1)).symm
        (ShiftedHom.comp (C := DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
          (edsEtale B S hS hsq).2)) (X := (edsEtaleRestrict B S hS hsq).obj E)
          (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
              ((pullbackComplexSmallEtale
              (edsEtaleHom B S hS hsq)).obj G) ((HomologicalComplex.single (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
              ℤ) 0).obj T.X₃)) x (DerivedCategory.triangleOfSESδ
              (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
              ℤ) 0).map T.f) ((HomologicalComplex.single (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
              ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex
              (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
              (edsEtaleHom B S hS hsq)).obj G))) (hex T hT)) (add_comm 1 i) :) =
      ((edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj T.X₃) (hN
          T.X₃) i).symm x).comp (DerivedCategory.triangleOfSESδ
          (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
          ℤ) 0).map T.f) ((HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
          ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex f
          G)) (hexX T hT)) (add_comm 1 i) :=
  edsRestrictCoefficientShiftedExt_symm_comp_triangleOfSESδ_mk hsq f G E
    ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).map T.f) ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
        ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T) (hexX T hT) (hex T hT)
    (hN T.X₁) (hN T.X₃) i x

/-- **`Ext^i_Y(L, ℱ) ≃+ Ext^i_X(E, 𝒢^• ⊗ f^*ℱ)` is compatible with the boundary maps.** -/
theorem edsRestricted_delta (hN : ∀ F : Modules.{u, u} B S hS Y.1 Y.2, CohomologySupportedOn
    B S hS X.1 X.2
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ))
      (tensorPullbackComplexDerived f G ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)))
        (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
        (((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ ((extPerfectCoefficientModulesFunctor B S hS
          (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
          (edsEtaleHom B S hS hsq)).obj G)).obj F)⟦i⟧)) (hex : ∀ T : ShortComplex
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)), T.ShortExact →
          ((T.map (HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (hexX : ∀ T : ShortComplex
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)), T.ShortExact →
        ((T.map (HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex f G)).ShortExact)
    (hδ : ∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom Linf ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (show ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
            (edsEtale B S hS hsq)) ((extPerfectCoefficientModulesFunctor B S hS
            (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale
            (edsEtaleHom B S hS hsq)).obj G)).obj T.X₃) i from Φ T.X₃ h₃ i e).comp
            (extPerfectCoefficientModulesDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) hex T hT) (add_comm 1 i))
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
    (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
    (e : ShiftedHom Linf ((DerivedCategory.singleFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i) :
    ((Φ T.X₁ h₁ (i + 1)).trans (edsRestrictCoefficientShiftedExt hsq f G E
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj T.X₁) (hN T.X₁) (i + 1)).symm) (e.comp hT.singleδ (add_comm 1 i)) =
      (((Φ T.X₃ h₃ i).trans (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₃) (hN T.X₃) i).symm) e).comp (DerivedCategory.triangleOfSESδ
        (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
        (tensorPullbackComplex f G)) (hexX T hT)) (add_comm 1 i) :=
  (congrArg (edsRestrictCoefficientShiftedExt hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up
      ℤ) 0).obj T.X₁) (hN T.X₁) (i + 1)).symm
      (edsRestricted_delta_aux B S hS hsq f G E Linf Φ hex T hT h₁ h₃ i e
        (hδ T hT h₁ h₂ h₃ i e))).trans
    (edsRestricted_delta_restrict B S hS hsq f G E hN hex hexX T hT i (Φ T.X₃ h₃ i e))

end Transport


/-! ### The data of Stacks 08JR (B) -/

/-- The data of Stacks 08JR (B) on the neighbourhood `V`, from a tower of perfect
approximations of `E|_V`, transported to `X`. -/
theorem exists_extPerfectDualTower_data_of_tower (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
      (hG : SmallEtaleFlatProperSupport B S hS f hf G)
    {Z : Set (points B S hS X.1)} {hZ : IsClosed Z} {V : Subfunctor X.1}
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
    (hZp : IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z)
    (tE : ℕ ⥤ smallEtaleModulesDerived B S hS (edsEtale B S hS hsq))
    (htE : ∀ n, SmallEtaleIsPerfect B S hS (tE.obj n))
    (cE : ∀ n, tE.obj n ⟶ ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq)))
    (hcomp : ∀ n, tE.map (homOfLE (Nat.le_succ n)) ≫ cE (n + 1) = cE n)
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
        IsIso ((smallEtaleModulesHomology B S hS (edsEtale B S hS hsq) j).map (cE n))) :
    ∃ (a : ℤ) (Linf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (ι : ∀ n, (extPerfectDualTower B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
          (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
          (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
            (fun _ => hZp)) tE htE).obj n ⟶ Linf)
      (_ : ∀ n, (extPerfectDualTower B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
          (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
          (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
            (fun _ => hZp)) tE htE).map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
      (_ : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).map (ι n)))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
          ShiftedHom E (tensorPullbackComplexDerived f G ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
            (ComplexShape.up ℤ) 0).obj F)) i),
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
          Φ F hF i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
            ((HomologicalComplex.single (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map q)))⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom Linf ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (Φ T.X₃ h₃ i e).comp (DerivedCategory.triangleOfSESδ
            (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.g)
            (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex f G))
              (shortExact_tensorPullbackComplex_map_single
                (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT))
              (add_comm 1 i)) := by
  have hGV := flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ
    hcompl (fun _ => hZp)
  obtain ⟨a, b, hab⟩ := hGV.bounded
  have hflat := FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hGV
  obtain ⟨Linf, ι, hιc, hι, hpc, Φ, -, h2, h3⟩ :=
    exists_isPseudoCoherent_extPerfectDual_of_coefficient B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
      (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
      (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY (edsRestrictComplex B S hS G hsq)
      hGV tE htE (tensorPullbackComplexNatTrans _ _)
      (isIso_extPerfectCoefficientComparison_tensorPullbackComplexNatTrans B S hS _ _ hGV)
      (fun _ => shortExact_tensorPullbackComplex_map_single hflat)
      (fun T hT => tensorPullbackComplexNatTrans_singleδ B S hS _ _ hflat T hT) a
      (fun n hn => hab n (Or.inl hn)) _ cE hcomp hcE
  have hNF := cohomologySupportedOn_tensorPullbackSingleDerived B S hS f G
    (fun q => (hGZ q).trans hcompl.symm.le)
  exact ⟨a, Linf, ι, hιc, hι, hpc, _,
    edsRestricted_naturality B S hS hsq f G E Linf hNF Φ h2,
    edsRestricted_delta B S hS hsq f G E Linf hNF Φ
      (fun _ => shortExact_tensorPullbackComplex_map_single hflat)
      (fun _ => shortExact_tensorPullbackComplex_map_single
        (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG)) h3⟩

/-- **The data of the proof of Stacks 08JR, part (B).**  Let `Y` be Noetherian, `f : X ⟶ Y`
locally of finite type and quasi-separated, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢^•` a bounded complex of
coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  There are

* a closed `Z ⊆ |X|` proper over `Y` containing the supports of the `𝒢ⁿ`, a quasi-compact open
  subspace `V ⊇ Z` and the elementary distinguished square `(X ∖ Z, V)`;
* a tower of perfect objects `tEₙ ⟶ E|_V` inducing isomorphisms on `Hʲ` for `j > -(n + 2)`;
* the tower `Lₙ = (R(f|_V)_* RSheafHom(tEₙ, 𝒢^•|_V))^∨`
  (`AlgebraicGeometry.Space.extPerfectDualTower`) with maps `ιₙ : Lₙ ⟶ L` inducing isomorphisms
  on `Hʲ` for `j > -(n + a)`, `L` pseudo-coherent;
* isomorphisms `Ext^i_Y(L, ℱ) ≃+ Ext^i_X(E, 𝒢^• ⊗ f^*ℱ)` for quasi-coherent `ℱ`, natural in `ℱ`
  and compatible with the boundary maps of short exact sequences of quasi-coherent modules. -/
theorem exists_extPerfectDualTower_data (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
      (hG : SmallEtaleFlatProperSupport B S hS f hf G) :
    ∃ (Z : Set (points B S hS X.1)) (hZ : IsClosed Z) (V : Subfunctor X.1)
      (_ : IsOpenSubspace B S hS V)
      (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
      (hZp : IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ)
      (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
      (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
      (hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z)
      (_ : Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι))
      (_ : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
      (tE : ℕ ⥤ smallEtaleModulesDerived B S hS (edsEtale B S hS hsq))
      (htE : ∀ n, SmallEtaleIsPerfect B S hS (tE.obj n))
      (cE : ∀ n, tE.obj n ⟶ ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
        (edsEtale B S hS hsq)))
      (_ : ∀ n, tE.map (homOfLE (Nat.le_succ n)) ≫ cE (n + 1) = cE n)
      (_ : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
        IsIso ((smallEtaleModulesHomology B S hS (edsEtale B S hS hsq) j).map (cE n)))
      (a : ℤ) (Linf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (ι : ∀ n, (extPerfectDualTower B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
          (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
          (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
            (fun _ => hZp)) tE htE).obj n ⟶ Linf)
      (_ : ∀ n, (extPerfectDualTower B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
          (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
          (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY
            (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
            (fun _ => hZp)) tE htE).map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
      (_ : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).map (ι n)))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
          ShiftedHom E (tensorPullbackComplexDerived f G ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
            (ComplexShape.up ℤ) 0).obj F)) i),
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
          Φ F hF i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
            ((HomologicalComplex.single (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map q)))⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom Linf ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (Φ T.X₃ h₃ i e).comp (DerivedCategory.triangleOfSESδ
            (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.g)
            (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex f G))
              (shortExact_tensorPullbackComplex_map_single
                (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT))
              (add_comm 1 i)) := by
  obtain ⟨Z, hZ, V, hV, hsq, hZp, hGZ, hVqc, hcompl, hZV⟩ :=
    exists_isOpenSubspace_isElementaryDistinguishedSquare_of_flatProperSupportComplex B S hS hTop f
      hf hY G hG
  have hN := isNoetherian_edsEtale_openSubspaceOfPoints B S hS hTop f hf hfqs hY hsq hVqc
  have hEV : SmallEtaleIsPseudoCoherent B S hS
      ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) :=
    isPseudoCoherent_edsEtaleRestrict_of_isCoherent_homology B S hS hsq hTop hN E hEcoh hEb
  obtain ⟨tE, htE, cE, hcomp, hcE⟩ :=
    exists_isPerfect_tower_smallEtale B S hS hTop (edsEtale B S hS hsq) hN.1 hN.2.1 hEV
  exact ⟨Z, hZ, V, hV, hsq, hZp, hGZ, hVqc, hcompl, hZV,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hTop Y.2 hY.2.1 hVqc _, tE, htE, cE, hcomp, hcE,
    exists_extPerfectDualTower_data_of_tower B S hS hTop f hf hfqs hY E G hG hsq hZp hGZ hVqc
      hcompl tE htE cE hcomp hcE⟩

/-- **Stacks 08JR, part (B).**  Let `S` be a scheme and `f : X ⟶ B` a morphism of algebraic spaces
over `S` with `B` Noetherian and `f` locally of finite type and quasi-separated.  Let
`E ∈ D^-_{Coh}(𝒪_X)` (coherent cohomology sheaves, bounded above) and let `𝒢^•` be a bounded
complex of coherent `𝒪_X`-modules, flat over `B`, with support proper over `B`.  Then there is a
pseudo-coherent `L ∈ D(𝒪_B)` with isomorphisms
`Ext^i_{𝒪_B}(L, ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢^• ⊗_{𝒪_X} f^*ℱ)` for quasi-coherent `𝒪_B`-modules `ℱ`,
functorial in `ℱ` and compatible with the boundary maps: for a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent modules, the boundary map of the distinguished triangle
of `ℱ₁[0] → ℱ₂[0] → ℱ₃[0]` on the left corresponds to the boundary map of the distinguished
triangle of the short exact sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0` on the right.

Here `Ext^i(A, C) = Hom(A, C[i])` in the derived categories of the small étale ringed sites,
`ℱ[0]` is `DerivedCategory.singleFunctor _ 0`, and `𝒢^• ⊗ f^*ℱ` is
`AlgebraicGeometry.Space.tensorPullbackComplex` at `ℱ` placed in degree `0`; the sequence of
complexes is written `ShortComplex.mk (ℱ₁[0] → ℱ₂[0]) (ℱ₂[0] → ℱ₃[0])` mapped by
`𝒢^• ⊗ f^*(-)`, exact by `AlgebraicGeometry.Space.shortExact_tensorPullbackComplex_map_single`. -/
@[stacks 08JR "(B)"]
theorem exists_isPseudoCoherent_extAddEquiv_tensorPullbackComplex (hTop : B.Contains
    (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    ∃ (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (L ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
          ShiftedHom E (tensorPullbackComplexDerived f G ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
            (ComplexShape.up ℤ) 0).obj F)) i),
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : L ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
          Φ F hF i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map q)))⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom L ((DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (Φ T.X₃ h₃ i e).comp (DerivedCategory.triangleOfSESδ
            (S := (ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.g)
            (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex f G))
              (shortExact_tensorPullbackComplex_map_single
                (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT))
              (add_comm 1 i)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Linf, -, -, -, hpc, Φ, h1, h2⟩ :=
    exists_extPerfectDualTower_data B S hS hTop f hf hfqs hY E hEcoh hEb G hG
  exact ⟨Linf, hpc, Φ, h1, h2⟩

end AlgebraicGeometry.Space

end
