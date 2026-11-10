module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTwistedRestrictScalarsTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FunctorTraceAlgebra
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCoreProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# The trace formula at the finite levels of the `O`-sheaf of a representation, twisted by `O`

Let `σ : π₁(X, x̄) → GL_m(O)` be a representation with coefficients in a finite free
`ℤ_ℓ`-algebra `O`, `ℱ_σ` its `O`-sheaf, `c ∈ O`, and `X` a separated scheme of finite type and
dimension at most one over a finite field `k`. The `n`-th level `ℱ_{σ,n}` is the restriction of
scalars of a constructible flat sheaf `G` of `Λ' = ℤ/ℓⁿ⁺¹ ⊗ O`-modules, on which `c` acts as the
scalar `1 ⊗ c` (`Stacks.EtaleCohomology.coeffLevelEtaleSheaf`). The trace formula of
[Stacks, Tag 03UG] for `G` over the finite ring `Λ'`, read through restriction of scalars twisted
by multiplication by `1 ⊗ c`, is the trace formula for `c_* ∘ π_X^*`:

`Tr_{ℤ/ℓⁿ⁺¹}(c_* ∘ π_X^* | RΓ_c(X_k̄, ℱ_{σ,n}))`
`= ∑_{x ∈ X(k)} Tr_{Λ'/(ℤ/ℓⁿ⁺¹)}((1 ⊗ c) · Tr_{Λ'}(π_x | G_x̄))`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.levelComplexMap`: a morphism of ℓ-adic sheaves on the
  complexes of the finite levels.
* `Stacks.EtaleCohomology.coeffLevelComplexRestrictIso`: the identification of the restriction
  of scalars of `G` with the `n`-th level.

## Main results

* `Stacks.EtaleCohomology.coeffLevel_twistedTraceFormula`: the trace formula for `c_* ∘ π_X^*` at
  the `n`-th level of `ℱ_σ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry
  AlgebraicGeometry.SmallEtale Stacks.ConstantSheaf Stacks.Frobenius

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Single

variable {V₁ V₂ : Type*} [Category* V₁] [Category* V₂] [HasZeroMorphisms V₁] [HasZeroMorphisms V₂]
  [HasZeroObject V₁] [HasZeroObject V₂] {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)
  (F : V₁ ⥤ V₂) [F.PreservesZeroMorphisms] (Θ : F ⟶ F) (j : ι)

/-- **`singleMapHomologicalComplex` is natural in endomorphisms of the functor.** -/
public theorem natTrans_mapHomologicalComplex_comp_singleMapHomologicalComplex (A : V₁) :
    (NatTrans.mapHomologicalComplex Θ c).app ((HomologicalComplex.single V₁ c j).obj A) ≫
        (HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A =
      (HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A ≫
        (HomologicalComplex.single V₂ c j).map (Θ.app A) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Θ.naturality_assoc]

end Single

section Levels

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- A morphism of ℓ-adic sheaves, on the complexes concentrated in degree `0` of the `n`-th
levels. -/
public def LAdicSheaf.levelComplexMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) (n : ℕ) :
    LAdicSheaf.levelComplex B X ℓ F n ⟶ LAdicSheaf.levelComplex B X ℓ G n :=
  ObjectProperty.homMk ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
      (φ.app n)))

end Levels

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}
  (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- The `n`-th level `G` as a complex of sheaves of `Λ'`-modules concentrated in degree `0`. -/
public abbrev coeffLevelComplex (n : ℕ) :
    CochainComplex.Plus (EtaleModules.{u, 0} (coeffLevelRing ℓ O (n + 1)) X.1) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj (coeffLevelEtaleSheaf b B X x e₀ σ hρ n),
    CochainComplex.plus_singleFunctor_obj _⟩

/-- **The restriction of scalars of `G` to `ℤ/ℓⁿ⁺¹` is the `n`-th level of `ℱ_ρ`**, as complexes
concentrated in degree `0`. -/
public def coeffLevelComplexRestrictIso (n : ℕ) :
    (etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1)))
        X.1).mapCochainComplexPlus.obj (coeffLevelComplex b B X x σ hρ n) ≅
      LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex
        (etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1)))
          X.1) (ComplexShape.up ℤ) 0).app (coeffLevelEtaleSheaf b B X x e₀ σ hρ n) ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (coeffLevelEtaleSheafRestrictIso b B X x e₀ σ hρ n))

/-- **Under the identification, multiplication by `1 ⊗ c` is the action of `c` on the level.** -/
public theorem coeffLevelComplexRestrictIso_smul (n : ℕ) (c : O) :
    etaleModuleRestrictScalarsComplexEndo (algebraMap (ZMod (ℓ ^ (n + 1)))
        (coeffLevelRing ℓ O (n + 1)))
        (restrictScalarsSMulNatTrans _ (coeffLevelRing.of ℓ O (n + 1) c))
        (coeffLevelComplex b B X x σ hρ n) ≫
        (coeffLevelComplexRestrictIso b B X x σ hρ n).hom =
      (coeffLevelComplexRestrictIso b B X x σ hρ n).hom ≫
        LAdicSheaf.levelComplexMap (representationLAdicSheafMap B X x e₀ hρ hρ
          (coefficientScalarRingHom b m c)
          (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) n := by
  refine ObjectProperty.hom_ext _ ?_
  have h :=
    coeffLevelEtaleSheafRestrictIso_smul b B X x e₀ σ hρ n (coeffLevelRing.of ℓ O (n + 1) c)
  rw [coeffLevelSheafMap_of] at h
  have h1 := natTrans_mapHomologicalComplex_comp_singleMapHomologicalComplex (ComplexShape.up ℤ)
    (etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1))) X.1)
    (etaleModuleRestrictScalarsNatTrans (algebraMap (ZMod (ℓ ^ (n + 1)))
      (coeffLevelRing ℓ O (n + 1)))
      (restrictScalarsSMulNatTrans _ (coeffLevelRing.of ℓ O (n + 1) c))
        X.1) 0 (coeffLevelEtaleSheaf b B X x e₀ σ hρ n)
  have h2 := congrArg (HomologicalComplex.single (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1)
    (ComplexShape.up ℤ) 0).map h
  rw [Functor.map_comp, Functor.map_comp] at h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- **The `Λ'`-sheaf `G`, placed in degree `0`, lies in `D_ctf(X, Λ')`.** -/
public theorem isCtf_coeffLevelComplex [Module.Finite ℤ_[ℓ] O] (n : ℕ) :
    IsCtf B (B.obj X.1 X.2) (coeffLevelRing ℓ O (n + 1))
      (DerivedCategory.Q.obj (coeffLevelComplex b B X x σ hρ n).obj) := by
  refine IsRepresentedByConstructibleFlatEtaleComplex.isCtf B _
    ⟨(coeffLevelComplex b B X x σ hρ n).obj, 0, 0, inferInstance, inferInstance, fun i => ?_,
      ⟨Iso.refl _⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact (isConstructibleFlatEtaleModule_coeffLevelEtaleSheaf b B X x σ hρ n).of_iso B X _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
  · exact isConstructibleFlatEtaleModule_of_isZero B _ X
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (J : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula at the `n`-th level of `ℱ_ρ`, twisted by `c ∈ O`**: for `X` of dimension
at most one over `k` and `ℓ ≠ p`, `RΓ_c(X_k̄, ℱ_{ρ,n})` is perfect and
`Tr(π_X^* ≫ c_* | RΓ_c(X_k̄, ℱ_{ρ,n}))`
`= ∑_{x ∈ X(k)} Tr_{Λ'/(ℤ/ℓⁿ⁺¹)}((1 ⊗ c) · Tr_{Λ'}(π_x | G_x̄))`, `G` the `n`-th level as a
sheaf of `Λ' = ℤ/ℓⁿ⁺¹ ⊗ O`-modules. -/
public theorem coeffLevel_twistedTraceFormula [Module.Free ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ 1) [Fintype (rationalPoints f)] (n : ℕ)
    (c : O) :
    ∃ (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar
          (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
            ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n))))
      (hKs : HasPerfectStalks (coeffLevelRing ℓ O (n + 1)) (coeffLevelComplex b B X x σ hρ n)),
      Stacks.Trace.commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
          (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_, hP⟩ (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar p q hcard
                (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
                  ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n) ≫
              (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).map
                (LAdicSheaf.levelComplexMap (representationLAdicSheafMap B X x e₀ hρ hρ
                  (coefficientScalarRingHom b m c)
                  (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) n)))) =
        ∑ y : rationalPoints f, Algebra.trace (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1))
          (coeffLevelRing.of ℓ O (n + 1) c *
            Stacks.Trace.commutativeAdditiveCommutatorQuotientEval (coeffLevelRing ℓ O (n + 1))
              (perfectDerivedTrace (coeffLevelRing ℓ O (n + 1))
                ⟨_, hKs (rationalGeometricPoint kbar y.1)⟩
                (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0}
                  (coeffLevelRing ℓ O (n + 1)) kbar p q hcard y.1
                  (coeffLevelComplex b B X x σ hρ n))))) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hΛ : (Nat.card (coeffLevelRing ℓ O (n + 1)) : k) ≠ 0 := by
    rw [Nat.card_congr (coeffLevelBasis ℓ b (n + 1)).equivFun.toEquiv, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow]
    refine pow_ne_zero _ (pow_ne_zero _ ?_)
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 hdvd).symm
  have hcore := curveTraceCore (coeffLevelRing ℓ O (n + 1)) k hΛ kbar p q hcard
  obtain ⟨hKs, hperf, htr⟩ := perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf
    (coeffLevelRing ℓ O (n + 1)) kbar p q hcard hcore B f hdim J
    (coeffLevelComplex b B X x σ hρ n) X.2 (isCtf_coeffLevelComplex b B X x σ hρ n)
  obtain ⟨hres, htw⟩ :=
    perfectDerivedTrace_canonicalCompactSupportFrobenius_comp_restrictScalarsEndo
      (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1)))
      (restrictScalarsSMulNatTrans _ (coeffLevelRing.of ℓ O (n + 1) c)) f J kbar p q hcard
      (preservesFiniteProjective_restrictScalars_algebraMap _ _) _ hperf
  let I := (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).mapIso
    (coeffLevelComplexRestrictIso b B X x σ hρ n)
  have hP := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso I).symm hres
  refine ⟨hP, hKs, ?_⟩
  have hcomm : DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar p q hcard
            ((etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ (n + 1)))
              (coeffLevelRing ℓ O (n + 1))) X.1).mapCochainComplexPlus.obj
              (coeffLevelComplex b B X x σ hρ n)) ≫
          (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).map
            (etaleModuleRestrictScalarsComplexEndo (algebraMap (ZMod (ℓ ^ (n + 1)))
              (coeffLevelRing ℓ O (n + 1)))
              (restrictScalarsSMulNatTrans _ (coeffLevelRing.of ℓ O (n + 1) c))
              (coeffLevelComplex b B X x σ hρ n))) ≫ (DerivedCategory.Plus.ι.mapIso I).hom =
      (DerivedCategory.Plus.ι.mapIso I).hom ≫ DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar p q hcard
            (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
              ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n) ≫
          (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).map
            (LAdicSheaf.levelComplexMap (representationLAdicSheafMap B X x e₀ hρ hρ
              (coefficientScalarRingHom b m c)
              (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) n)) := by
    have hπ := (canonicalCompactSupportFrobeniusNatTrans.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar p q
      hcard).naturality (coeffLevelComplexRestrictIso b B X x σ hρ n).hom
    have hψ := congrArg (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).map
      (coeffLevelComplexRestrictIso_smul b B X x σ hρ n c)
    rw [Functor.map_comp, Functor.map_comp] at hψ
    simp only [Functor.mapIso_hom, ← Functor.map_comp, I]
    congr 1
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hψ).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hπ.symm).trans (Category.assoc _ _ _))))
  refine (congrArg _ (perfectDerivedTrace_congr _ ⟨_, hres⟩ ⟨_, hP⟩
    (DerivedCategory.Plus.ι.mapIso I) _ _ hcomm).symm).trans ?_
  refine (congrArg _ htw).trans ?_
  refine (congrArg (fun z => Stacks.Trace.commutativeAdditiveCommutatorQuotientEval
    (ZMod (ℓ ^ (n + 1))) (functorTraceMap (ModuleCat.restrictScalars.{u + 1}
      (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1))))
      (restrictScalarsSMulNatTrans _ (coeffLevelRing.of ℓ O (n + 1) c))
      (preservesFiniteProjective_restrictScalars_algebraMap _ _) z)) htr).trans ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact eval_functorTraceMap_restrictScalarsSMulNatTrans _ _ _ _

end Stacks.EtaleCohomology

end
