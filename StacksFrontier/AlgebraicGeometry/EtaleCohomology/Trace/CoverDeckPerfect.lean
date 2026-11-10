module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectCurveFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckConjugacyTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness of the constant-coefficient complexes in Steps 8 and 9 of Tag 03UG

The conjugacy-trace vanishing of Steps 8 and 9 of the proof of [Stacks, Tag 03UG]
(`Stacks.EtaleCohomology.conjugacyTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero`)
takes the traces of endomorphisms of `RΓ(V̄_k̄, ℤ/ℓⁿ)`, `RΓ((V̄ ∖ V)_k̄, ℤ/ℓⁿ)`,
`RΓ_c(V_k̄, ℤ/ℓⁿ)` and `Γ(Spec k̄, ℤ/ℓⁿ)`, for the smooth projective compactification `V̄` of a
connected Galois cover `V` of a curve. These complexes are perfect: the first three are
compactly supported cohomology of the constant sheaf `ℤ/ℓⁿ`, which is flat and constructible, on
schemes of dimension at most one
(`isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_topologicalKrullDim_le_one`),
and the last is `ℤ/ℓⁿ` in degree zero.

## Main results

* `Stacks.EtaleCohomology.isPerfect_selfMapCohomology_etaleModuleConstantComplex_zmod`:
  `RΓ(Y_k̄, ℤ/ℓⁿ)` is perfect for a proper scheme `Y` of dimension at most one over a finite field.
* `Stacks.EtaleCohomology.isPerfect_extensionByZeroConstantComplex_zmod`: `RΓ_c(V_k̄, ℤ/ℓⁿ)` is
  perfect for an open `V` of such a `Y`.
* `Stacks.EtaleCohomology.isPerfect_baseSectionsComplex_etaleModuleConstantComplex_zmod`:
  `Γ(Spec k̄, ℤ/ℓⁿ)` is perfect.
* `map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero_of_isPerfect`:
  the conjugacy-trace vanishing of Steps 8 and 9, granted the perfectness of
  `RΓ_c(U_k̄, D(A[H]))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius Stacks.ZModPrimePower Stacks.InverseSystem CategoryTheory.FilteredDerived

universe u r

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Constant

variable (ℓ n : ℕ) [Fact ℓ.Prime] [NeZero n]

omit [NeZero n] in
/-- The constant sheaf `(ℤ/ℓⁿ)_X` with value the free module of rank one is flat. -/
theorem powExact_constantSheaf_zmod (X : Scheme.{u}) :
    PowExact ℓ n ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ n)))).obj
      (ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n))))) := by
  let M := ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n)))
  have hM : (ℓ ^ n) • 𝟙 M = 0 := by
    ext x
    change ((ℓ ^ n) • x).down = (0 : ULift.{u + 1} (ZMod (ℓ ^ n))).down
    rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ n)), ZMod.natCast_self, zero_smul]
  have hM' : IsPowExact ℓ n M :=
    (isPowExact_finsupp (Unit)).of_addEquiv
      ((Finsupp.uniqueLinearEquiv (ZMod (ℓ ^ n)) (ZMod (ℓ ^ n)) ()).toAddEquiv.trans
        AddEquiv.ulift.symm)
  exact PowExact.map _ hM (powExact_of_isPowExact hM')

section
attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
/-- **The constant sheaf `Λ_X` is constructible** on a quasi-compact quasi-separated member of a
big étale site: it is `j_!Λ` for `j` the identity (Stacks 03S8). -/
theorem isBigSiteConstructibleEtaleModule_constantSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (Λ : Type r) [CommRing Λ]
    [IsNoetherianRing Λ] :
    IsBigSiteConstructibleEtaleModule.{u, r} B X Λ ((constantSheaf X.obj.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ)).obj (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))) :=
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule.{u, r} B X Λ
  (IsBigSiteConstructibleEtaleModule B X Λ).prop_of_iso
    ((etaleModuleExtensionByZeroIdIso.{u, r} Λ X.obj).app _)
    (isConstructibleEtaleModule_etaleModuleShriekConstant_of_contains Λ B X.property X.property
      (𝟙 X.obj))
end

/-- `RΓ_c(V_k̄, ℤ/ℓⁿ)` is perfect for the constant sheaf on a compactified scheme `V` of
dimension at most one over a finite field. -/
private theorem isPerfect_compactSupportFrobeniusCohomology_constantSheaf {k : Type u} [Field k]
    [Finite k] {V : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V] (f : V ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (J : CompactificationOf (Over.mk f)) (hdim : topologicalKrullDim V ≤ 1) (kbar : Type u)
    [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ n)) f J kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ n)))).obj
            (ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n))))),
          CochainComplex.plus_singleFunctor_obj _⟩)) := by
  let B := BigEtaleSite.containing V
  let X := B.obj V (BigEtaleSite.contains_containing V)
  have : CompactSpace X.obj := inferInstanceAs (CompactSpace V)
  have : QuasiSeparatedSpace X.obj := inferInstanceAs (QuasiSeparatedSpace V)
  exact isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_topologicalKrullDim_le_one
    B X f J kbar ℓ n hdim _ (powExact_constantSheaf_zmod ℓ n V)
    (isBigSiteConstructibleEtaleModule_constantSheaf B X _)

/-- **`RΓ(Y_k̄, ℤ/ℓⁿ)` is perfect** for a proper scheme `Y` of dimension at most one over a
finite field `k`, in the form `RΓ(Spec k̄, R(Y_k̄ ⟶ Spec k̄)_* (ℤ/ℓⁿ)_{Y_k̄})` with the constant
sheaf pulled back from `Spec k̄`. -/
@[sga "5 XII 6.1" "special case"]
theorem isPerfect_selfMapCohomology_etaleModuleConstantComplex_zmod {k : Type u} [Field k]
    [Finite k] (Y : Over (Spec (.of k))) [IsProper Y.hom]
    (hdim : topologicalKrullDim Y.left ≤ 1) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n)) (pullback.snd Y.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))) := by
  let Λ := ZMod (ℓ ^ n)
  let M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have hP := isPerfect_compactSupportFrobeniusCohomology_constantSheaf ℓ n Y.hom
    (CompactificationOf.ofProper Y.hom) hdim kbar
  let F := (constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let fst := pullback.fst Y.hom (specAlgebraMap k kbar)
  let snd := pullback.snd Y.hom (specAlgebraMap k kbar)
  let sp := fun {A B : Type _} [Category A] [Category B] [Abelian A] [Abelian B] (G : A ⥤ B)
    [G.PreservesZeroMorphisms] (N : A) =>
      (singlePlusFunctorCompMapCochainComplexPlusIso G).app N
  let eL := (etaleModuleInverseImage.{u, 0} Λ fst).mapCochainComplexPlus.mapIso
      (sp (etaleModuleExtensionByZero.{u, 0} Λ (𝟙 Y.left)) F) ≪≫
    sp (etaleModuleInverseImage.{u, 0} Λ fst) _ ≪≫
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
      ((etaleModuleInverseImage.{u, 0} Λ fst).mapIso
        ((etaleModuleExtensionByZeroIdIso Λ Y.left).app F) ≪≫
        (etaleModuleInverseImageConstantIso.{u, 0} Λ fst).app M)
  let eR := (etaleModuleInverseImage.{u, 0} Λ snd).mapCochainComplexPlus.mapIso
      (sp (constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) M) ≪≫
    sp (etaleModuleInverseImage.{u, 0} Λ snd) _ ≪≫
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} Λ snd).app M)
  exact StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ snd).mapIso
        (DerivedCategory.Plus.Q.mapIso (eR ≪≫ eL.symm))))) hP

/-- **`RΓ_c(V_k̄, ℤ/ℓⁿ)` is perfect** for an open `V` of a proper scheme `Y` of dimension at most
one over a finite field, in the form `RΓ(Y_k̄, (j_{V!} j_V^{-1} ℤ/ℓⁿ)|_{Y_k̄})`. -/
theorem isPerfect_extensionByZeroConstantComplex_zmod {k : Type u} [Field k] [Finite k]
    (Y : Over (Spec (.of k))) [IsProper Y.hom] (hdim : topologicalKrullDim Y.left ≤ 1)
    {V : Scheme.{u}} (jV : V ⟶ Y.left) [IsOpenImmersion jV] (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
          (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) Y jV
                (zmodSingleComplex.{u} ℓ n))))))) := by
  let Λ := ZMod (ℓ ^ n)
  let M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (jV ≫ Y.hom)
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated (jV ≫ Y.hom)
  let jY : CompactificationOf (Over.mk (jV ≫ Y.hom)) :=
    ⟨StructuredArrow.mk (Y := Over.mk Y.hom)
      (Over.homMk (U := Over.mk (jV ≫ Y.hom)) (V := Over.mk Y.hom) jV rfl),
      ⟨inferInstanceAs (IsOpenImmersion jV), inferInstanceAs (IsProper Y.hom)⟩⟩
  have hdimV : topologicalKrullDim V ≤ 1 :=
    jV.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hP := isPerfect_compactSupportFrobeniusCohomology_constantSheaf ℓ n (jV ≫ Y.hom) jY hdimV
    kbar
  let F := (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let sp := fun {A B : Type _} [Category A] [Category B] [Abelian A] [Abelian B] (G : A ⥤ B)
    [G.PreservesZeroMorphisms] (N : A) =>
      (singlePlusFunctorCompMapCochainComplexPlusIso G).app N
  let e : (etaleModuleRestriction.{u, 0} Λ jV).mapCochainComplexPlus.obj
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj
        (zmodSingleComplex.{u} ℓ n)) ≅ (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F :=
    (etaleModuleRestriction.{u, 0} Λ jV).mapCochainComplexPlus.mapIso
        (sp (constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) M) ≪≫
      sp (etaleModuleRestriction.{u, 0} Λ jV) _ ≪≫
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jV).symm.app _ ≪≫
          (etaleModuleInverseImageConstantIso.{u, 0} Λ jV).app M)
  exact StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso
          ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.mapIso
            ((etaleModuleExtensionByZero.{u, 0} Λ jV).mapCochainComplexPlus.mapIso e)))))) hP

omit [NeZero n] in
/-- **`Γ(Spec k̄, ℤ/ℓⁿ)` is perfect**: it is `ℤ/ℓⁿ` placed in degree zero, for `ℓ` invertible in
the algebraically closed field `k̄`. -/
theorem isPerfect_baseSectionsComplex_etaleModuleConstantComplex_zmod (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] (hℓ : (ℓ : kbar) ≠ 0) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
      (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj)) := by
  let Λ := ZMod (ℓ ^ n)
  let M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  let c := constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let G := sheafToPresheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (CategoryTheory.evaluation (Spec (.of kbar)).Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of kbar)))))
  have hN : ((ℓ ^ n : ℕ) : kbar) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hℓ
  obtain ⟨eS⟩ := nonempty_constantSections_addEquiv (Ω := kbar) (ℓ ^ n) hN
  let eL : G.obj (c.obj M) ≃ₗ[Λ] Λ :=
    { eS with map_smul' := (eS.toAddMonoidHom.toZModLinearMap (ℓ ^ n)).map_smul }
  have : Module.Finite Λ (G.obj (c.obj M)) := Module.Finite.equiv eL.symm
  have : Module.Projective Λ (G.obj (c.obj M)) := Module.Projective.of_equiv eL.symm
  have hP := isPerfect_Q_single_of_projective (G.obj (c.obj M))
  refine StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso ?_) hP
  exact (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex c (ComplexShape.up ℤ) 0).app M) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app (c.obj M)

end Constant

/-! ### Steps 8 and 9 with the constant-coefficient perfectness discharged -/

section CoverDeck

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U : Scheme.{u}} {H : Type} [Group H]
  [Fintype H] {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU]
  (J : CompactificationOf (Over.mk pU))
  (G : EtaleGaloisCovering U H) [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  [ConnectedSpace ((𝟭 Scheme).obj G.cover.left)]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **`Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, D(A[H])))` dies in every quotient killed by `ℓ^m`**, for
`A = ℤ/ℓⁿ` with `n ≥ m + v` whenever `ℓ^v` divides `#H` and `U(k) = ∅`, granted the
perfectness of `RΓ_c(U_k̄, D(A[H]))` over `A[H]`. -/
theorem map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero_of_isPerfect
    [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)]
    (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf))))
    {m : ℕ} {M : Type*} [AddCommGroup M]
    (Ψ : AdditiveCommutatorQuotient (MonoidAlgebra (ZMod (ℓ ^ n)) H) →+ M)
    (hM : ∀ y : M, (ℓ ^ m) • y = 0) (hnm : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card H → m + v ≤ n) :
    Ψ (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H) ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
          (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf)))) = 0 := by
  have : NeZero n := ⟨by lia⟩
  have : IsProper (Over.mk J.toBase).hom := inferInstanceAs (IsProper J.toBase)
  obtain ⟨C⟩ := nonempty_coverCompactification k pU (Over.mk J.toBase).hom J.immersion
    (show J.immersion ≫ (Over.mk J.toBase).hom = pU from Over.w J.obj.hom)
    (G.cover.hom : G.cover.left ⟶ U)
  have : IsProper C.toOver.hom := C.isProper
  have : IsProper C.boundaryOver.hom := inferInstanceAs (IsProper (C.boundaryι ≫ C.q))
  have hdim : topologicalKrullDim C.toOver.left ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one C.q).le
  have hdimW : topologicalKrullDim C.boundaryOver.left ≤ 1 :=
    C.boundaryι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hℓ' : (ℓ : kbar) ≠ 0 := by
    rw [← map_natCast (algebraMap k kbar)]
    exact (map_ne_zero _).2 hℓ
  exact map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero J G C kbar
    p q hcard ℓ n hℓ hn hperf
    (isPerfect_extensionByZeroConstantComplex_zmod ℓ n C.toOver hdim C.j kbar)
    (isPerfect_selfMapCohomology_etaleModuleConstantComplex_zmod ℓ n C.toOver hdim kbar)
    (isPerfect_selfMapCohomology_etaleModuleConstantComplex_zmod ℓ n C.boundaryOver hdimW kbar)
    (isPerfect_baseSectionsComplex_etaleModuleConstantComplex_zmod ℓ n kbar hℓ') Ψ hM hnm

end CoverDeck

end Stacks.EtaleCohomology

end
