module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.IntegralCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Vanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# Higher direct images of torsion sheaves of modules along proper morphisms

Let `Λ` be a ring in which every element is killed by a positive integer, for instance `ℤ/nℤ`
with `n > 0`, and let `p : S ⟶ T` be a morphism of schemes. A sheaf of `Λ`-modules on `S_étale`
is then a torsion abelian sheaf, and its higher direct images as a sheaf of `Λ`-modules are
those of its underlying abelian sheaf. So a vanishing statement for the higher direct images of
torsion abelian sheaves gives the same statement for sheaves of `Λ`-modules; applied to
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim`
it bounds the cohomological dimension of `Rp_*` on sheaves of `Λ`-modules for a proper `p` of
bounded fibre dimension.

## Main results

* `isZero_rightDerived_etaleModuleDirectImage_of_abelian`: if `R^q p_*` kills every torsion
  abelian sheaf on `S_étale`, it kills every sheaf of `Λ`-modules.
* `exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_fiberDim`: for `p` proper
  with fibres of dimension at most `N`, `R^q p_*` vanishes on sheaves of `Λ`-modules in all
  degrees `q ≥ 2N + 1`.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u r

namespace Stacks.EtaleCohomology

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for the
direct image of abelian sheaves.** For `I` injective in sheaves of `Λ`-modules on `S_étale` and
any morphism of schemes `p : S ⟶ T`, `R^q p_* (I_ab) = 0` for every `q > 0`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_forgetToAbelian_of_injective
    (Λ : Type r) [CommRing Λ] {S T : Scheme.{u}} (p : S ⟶ T)
    (I : EtaleModules.{u, r} Λ S) [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj
      ((etaleModuleForgetToAbelian.{u, r} Λ S).obj I)) := by
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, r} S
  let := IsGrothendieckAbelian.hasExt.{max (u + 1) r}
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
  let := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, r}
    (J := S.smallEtaleTopology)
  obtain ⟨q, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  exact IsZero.of_iso
    (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{r}
      T.smallEtaleTopology S.smallEtaleTopology (smallEtaleBaseChange p)
      (etaleConstantRingSheaf.{u, r} Λ S) ((etaleModuleSheafEquivalence.{u, r} Λ S).functor.obj I)
      q)
    (((etaleAbelianDirectImage.{u, r} p).rightDerived (q + 1)).mapIso
      ((etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ S).app I).symm)

/-- **Higher direct images of sheaves of `Λ`-modules from those of torsion abelian sheaves.**
Let `Λ` be a ring every element of which is killed by a positive integer, let `p : S ⟶ T` be a
morphism of schemes and `q` a degree. If `R^q p_*` kills every torsion abelian sheaf on
`S_étale`, then it kills every sheaf of `Λ`-modules on `S_étale`. -/
theorem isZero_rightDerived_etaleModuleDirectImage_of_abelian (Λ : Type r) [CommRing Λ]
    (hΛ : ∀ x : Λ, ∃ n : ℕ, 0 < n ∧ (n : Λ) * x = 0) {S T : Scheme.{u}} (p : S ⟶ T) (q : ℕ)
    (h : ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
      Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F →
        IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (F : EtaleModules.{u, r} Λ S) :
    IsZero (((etaleModuleDirectImage.{u, r} Λ p).rightDerived q).obj F) := by
  have htors : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology
      ((etaleModuleForgetToAbelian.{u, r} Λ S).obj F) := by
    intro U x
    obtain ⟨n, hn, hn1⟩ := hΛ 1
    refine ⟨⊤, (S.smallEtaleTopology).top_mem U, fun V f _ ↦ ⟨n, hn, ?_⟩⟩
    change n • (F.obj.map f.op x : F.obj.obj (Opposite.op V)) = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, ← mul_one (n : Λ), hn1, zero_smul]
  have hac : ∀ I : EtaleModules.{u, r} Λ S, Injective I →
      (etaleAbelianDirectImage.{u, r} p).rightAcyclic
        ((etaleModuleForgetToAbelian.{u, r} Λ S).obj I) := fun I _ ↦
    (rightAcyclic_iff_isZero_rightDerived _ _).2 fun k hk ↦
      isZero_rightDerived_etaleAbelianDirectImage_forgetToAbelian_of_injective Λ p I k hk
  have e₁ := ((Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
    (etaleModuleForgetToAbelian.{u, r} Λ S) (etaleAbelianDirectImage.{u, r} p) hac q).app F)
  obtain ⟨e₂⟩ := rightDerived_comp_iso_of_preservesHomology
    (etaleModuleDirectImage.{u, r} Λ p) (etaleModuleForgetToAbelian.{u, r} Λ T) q F
  exact isZero_of_faithful (etaleModuleForgetToAbelian.{u, r} Λ T)
    ((h _ htors).of_iso (e₂ ≪≫ e₁))

/-- **Finite cohomological dimension of `Rp_*` on torsion sheaves of modules, for `p` proper of
bounded fibre dimension.** Let `Λ` be a ring every element of which is killed by a positive
integer and let `p : S ⟶ T` be a proper morphism of schemes all of whose fibres have dimension
at most `N`. Then `R^q p_* F = 0` for every sheaf of `Λ`-modules `F` on `S_étale` and every
`q ≥ 2N + 1`. -/
theorem exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_fiberDim
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    (Λ : Type r) [CommRing Λ] (hΛ : ∀ x : Λ, ∃ n : ℕ, 0 < n ∧ (n : Λ) * x = 0)
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (N : ℕ)
    (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ S,
      IsZero (((etaleModuleDirectImage.{u, r} Λ p).rightDerived q).obj F) :=
  ⟨2 * N + 1, fun q hq F ↦
    isZero_rightDerived_etaleModuleDirectImage_of_abelian Λ hΛ p q
      (fun G hG ↦ isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim.{u, r}
        h095T h03SC p N hN G hG q (by omega)) F⟩

end Stacks.EtaleCohomology

end
