module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsOfSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFormalFunctionsDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsModuleULift
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomSupportIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# Full faithfulness of the completion functor on an algebraic space

Stacks 08B9: in Situation 08B7 — `A` Noetherian and `I`-adically complete, `X` separated and of
finite type over `Spec A`, `𝓘 = I 𝒪_X` — the completion functor
`Coh(𝒪_X) ⟶ Coh(X, 𝓘)` of Stacks 08B4 is bijective on `Hom(M, N)` as soon as
`Supp M ∩ Supp N` is proper over `Spec A`.

This first part is the reduction of the source: by Stacks 08B6
(`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfNoetherian`), bijectivity of the
completion functor on `Hom(M, N)` follows from the theorem on formal functions in degree zero for
the internal hom `𝓗om(M, N)`, that is, from bijectivity of
`AlgebraicGeometry.Space.adicSectionsOfSections` for it.

## Main results

* `AlgebraicGeometry.Space.completionFunctor_map_eq` — the completion of `a : M ⟶ N` is the
  image under the identification of Stacks 08B6 of the global section of `𝓗om(M, N)` given by `a`.
* `AlgebraicGeometry.Space.bijective_completionFunctor_map_of_bijective_adicSectionsOfSections` —
  the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasCokernels_modules hasCokernels_modules_succ
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section Reduction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)

/-- A morphism of the inverse systems of ideal-power quotients presented by their successive
transition maps is a morphism of the systems of `AlgebraicGeometry.Space.adicQuotientSystem`: the
two functors out of `ℕᵒᵖ` have the same terms and the same successive transition maps. -/
def smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom {M N : Modules.{u, u} B S hS X.1 X.2}
    (γ : smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 M ⟶
      smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 N) :
    adicQuotientSystem B S hS X.1 X.2 𝓘 M ⟶ adicQuotientSystem B S hS X.1 X.2 𝓘 N :=
  NatTrans.ofOpSequence (fun n => γ.app (op n)) fun n => by
    have h := γ.naturality (homOfLE (n.le_add_right 1)).op
    rw [smallEtaleAdicQuotientSystem_map_succ, smallEtaleAdicQuotientSystem_map_succ] at h
    exact h

/-- The component at `n` of
`AlgebraicGeometry.Space.smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom γ` is the
component of `γ` at `n`. -/
@[simp]
theorem smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom_app
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (γ : smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 M ⟶
      smallEtaleAdicQuotientSystem B S hS X.1 X.2 𝓘 N) (n : ℕ) :
    (smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom B S hS X 𝓘 γ).app (op n) =
      γ.app (op n) :=
  rfl

/-- Two morphisms of functors out of `ℕᵒᵖ` are equal if their components at every `op n` are. -/
private theorem natTrans_ext_of_app_op {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C} {a b : F ⟶ G}
    (h : ∀ n : ℕ, a.app (op n) = b.app (op n)) : a = b :=
  NatTrans.ext (funext fun ⟨n⟩ => h n)

/-- `AlgebraicGeometry.Space.smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom` is a
bijection from the morphisms `smallEtaleAdicQuotientSystem M ⟶ smallEtaleAdicQuotientSystem N`
to the morphisms `adicQuotientSystem M ⟶ adicQuotientSystem N`. -/
theorem bijective_smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom
    (M N : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective (smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom B S hS X 𝓘
      (M := M) (N := N)) := by
  refine ⟨fun γ γ' h => natTrans_ext_of_app_op fun n => ?_, fun δ => ?_⟩
  · exact congrArg (fun k : adicQuotientSystem B S hS X.1 X.2 𝓘 M ⟶
      adicQuotientSystem B S hS X.1 X.2 𝓘 N => k.app (op n)) h
  · refine ⟨NatTrans.ofOpSequence (fun n => δ.app (op n)) fun n => ?_,
      natTrans_ext_of_app_op fun n => rfl⟩
    rw [smallEtaleAdicQuotientSystem_map_succ, smallEtaleAdicQuotientSystem_map_succ]
    exact δ.naturality (homOfLE (n.le_add_right 1)).op

variable [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ X.1)
  (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
  (M N : CoherentModules.{u, u} B S hS X.1 X.2)

include hZ hFN in
/-- **The completion of `a : M ⟶ N` is read off the global section of `𝓗om(M, N)` given by `a`**,
through the identification of Stacks 08B6. -/
theorem completionFunctor_map_eq (a : M ⟶ N) :
    ((completionFunctor B S hS X.1 X.2 𝓘 hI).map a).hom =
      smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom B S hS X 𝓘
        (smallEtaleInternalHomAdicEquivOfNoetherian B S hS X 𝓘 M.obj N.obj hZ hFN hI
            M.property N.property
          (adicSectionsOfSections B S hS X.1 X.2 𝓘
            (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj)
            ((smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj N.obj).symm a.hom))) := by
  let σ := (smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj N.obj).symm a.hom
  let t : { γ : ∀ n : ℕ, smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) M.obj ⟶
        smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N.obj //
      ∀ n : ℕ, smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) M.obj ≫ γ n =
        γ (n + 1) ≫ smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) N.obj } :=
    ⟨fun n => idealPowerQuotientMapOfHom B S hS X.1 X.2 𝓘 (n + 1) a.hom, fun n =>
      idealPowerQuotientMapOfLE_comp_idealPowerQuotientMapOfHom B S hS X.1 X.2 𝓘
        (Nat.le_succ (n + 1)) a.hom⟩
  have key : adicSectionsMap B S hS X.1 X.2 _ _ _ _
        (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M.obj N.obj)
        (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M.obj N.obj)
        (adicSectionsOfSections B S hS X.1 X.2 𝓘
          (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj) σ) =
      smallEtaleInternalHomAdicSection B S hS X.1 X.2 𝓘 M.obj N.obj t := by
    refine Subtype.ext (funext fun n => ?_)
    apply (smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj
      (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N.obj)).injective
    change smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj _
        (SheafOfModules.sectionsMap (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘
          M.obj N.obj n) (SheafOfModules.sectionsMap
            (smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 (n + 1)
              (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj)) σ)) =
      smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj _
        ((smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj _).symm
          (smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 (n + 1) M.obj ≫ t.1 n))
    rw [Equiv.apply_symm_apply, ← SheafOfModules.sectionsMap_comp,
      smallEtaleAdicQuotientProjection_comp_comparisonApp, smallEtaleInternalHomSectionsEquiv_map,
      Equiv.apply_symm_apply]
    exact (π_comp_idealPowerQuotientMapOfHom B S hS X.1 X.2 𝓘 (n + 1) a.hom).symm
  have hE : smallEtaleInternalHomAdicEquivOfNoetherian B S hS X 𝓘 M.obj N.obj hZ hFN hI
      M.property N.property (adicSectionsOfSections B S hS X.1 X.2 𝓘
        (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj) σ) =
      (systemHomEquiv B S hS X.1 X.2 _ _ _ _).symm t := by
    change (systemHomEquiv B S hS X.1 X.2 _ _ _ _).symm
      ((Equiv.ofBijective _ (bijective_smallEtaleInternalHomAdicSection B S hS X.1 X.2 𝓘 M.obj
        N.obj)).symm (adicSectionsMap B S hS X.1 X.2 _ _ _ _
          (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M.obj N.obj)
          (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M.obj N.obj)
          (adicSectionsOfSections B S hS X.1 X.2 𝓘
            (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj) σ))) = _
    rw [key]
    congr 1
    exact (Equiv.ofBijective _ (bijective_smallEtaleInternalHomAdicSection B S hS X.1 X.2 𝓘 M.obj
        N.obj)).symm_apply_apply t
  rw [hE]
  exact natTrans_ext_of_app_op fun n => rfl

include hZ hFN in
/-- **The reduction of Stacks 08B9 to the theorem on formal functions for `𝓗om(M, N)`.**  If
`H⁰(X, 𝓗om(M, N)) ⟶ limₙ H⁰(X, 𝓗om(M, N) / 𝓘ⁿ⁺¹ 𝓗om(M, N))` is bijective, then the completion
functor is bijective on `Hom(M, N)`. -/
theorem bijective_completionFunctor_map_of_bijective_adicSectionsOfSections
    (h : Function.Bijective (adicSectionsOfSections B S hS X.1 X.2 𝓘
      (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj))) :
    Function.Bijective (fun a : M ⟶ N => (completionFunctor B S hS X.1 X.2 𝓘 hI).map a) := by
  let E := smallEtaleInternalHomAdicEquivOfNoetherian B S hS X 𝓘 M.obj N.obj hZ hFN hI
    M.property N.property
  let Φ : (M ⟶ N) → ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj M ⟶
      (completionFunctor B S hS X.1 X.2 𝓘 hI).obj N) := fun a =>
    ObjectProperty.homMk (smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom B S hS X 𝓘
      (E (adicSectionsOfSections B S hS X.1 X.2 𝓘
        (smallEtaleInternalHom B S hS X.1 X.2 M.obj N.obj)
        ((smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj N.obj).symm a.hom))))
  have hΦ : (fun a : M ⟶ N => (completionFunctor B S hS X.1 X.2 𝓘 hI).map a) = Φ := by
    funext a
    exact InducedCategory.hom_ext (completionFunctor_map_eq B S hS X 𝓘 hZ hFN hI M N a)
  rw [hΦ]
  have h1 : Function.Bijective (fun a : M ⟶ N => a.hom) :=
    ⟨fun a b hab => InducedCategory.hom_ext hab, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have h5 : Function.Bijective (fun g : adicQuotientSystem B S hS X.1 X.2 𝓘 M.obj ⟶
      adicQuotientSystem B S hS X.1 X.2 𝓘 N.obj =>
      (ObjectProperty.homMk g : (completionFunctor B S hS X.1 X.2 𝓘 hI).obj M ⟶
        (completionFunctor B S hS X.1 X.2 𝓘 hI).obj N)) :=
    ⟨fun g g' hg => congrArg (fun k => k.hom) hg, fun b => ⟨b.hom, rfl⟩⟩
  exact h5.comp ((bijective_smallEtaleAdicQuotientSystemHomToAdicQuotientSystemHom B S hS X 𝓘
    M.obj N.obj).comp (E.bijective.comp (h.comp
      ((smallEtaleInternalHomSectionsEquiv B S hS X.1 X.2 M.obj N.obj).symm.bijective.comp h1))))

end Reduction

/-! ### Formal functions in degree zero for a module with proper support -/

section ProperSupport

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A]
  {hA : B.Contains (Spec (.of A))} (X : AlgebraicSpaces B (Spec (.of A)) hA)

/-- An algebraic space locally of finite type over a Noetherian ring is locally Noetherian, in the
form of the `Fact` instance the completion functor of Stacks 08B4 is stated with. -/
theorem fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA
      ((isTerminal_yoneda_obj_base B _ hA).from X.1)) :
    Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B _ hA X.2 (isAlgebraicSpace_yoneda B _ hA _) _
      hft (hasEtaleLocalProperty_isLocallyNoetherian_base A)⟩

/-- An algebraic space separated and of finite type over a Noetherian ring is Noetherian. -/
theorem isNoetherian_of_isFiniteType_of_isSeparated_toBase
    (hft : IsFiniteType B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    (hsep : IsSeparated B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1)) :
    IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1 :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact_toBase B _ hA _ hft.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B _ hA B.contains_terminal _
      X.2 (isAffineSpace_yoneda B _ hA _ (inferInstanceAs (IsAffine (Spec (.of A)))))
      (isQuasiSeparated_of_isSeparated B _ hA hsep),
    isLocallyNoetherian_of_isLocallyOfFiniteType B _ hA X.2 (isAlgebraicSpace_yoneda B _ hA _) _
      hft.1 (hasEtaleLocalProperty_isLocallyNoetherian_base A)⟩

variable (I : Ideal A) [IsAdicComplete I A]

/-- **The theorem on formal functions in degree zero for a coherent module with proper support**:
for `X` locally of finite type over a Noetherian ring `A` complete with respect to `I`, and a
coherent `K` whose support is proper over `Spec A`,
`Γ(X, K) ⟶ limₙ Γ(X, K / (I 𝒪_X)ⁿ⁺¹ K)` is bijective.

Stacks 0CZI writes `K = i_* G` for a closed subspace `i : Z ⟶ X` proper over `Spec A`; the
statement for `G` on the proper `Z` is
`AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_isProper`, and it passes to the
direct image by
`AlgebraicGeometry.Space.bijective_adicSectionsOfSections_closedSubspacePushforward`. -/
theorem bijective_adicSectionsOfSections_of_hasProperSupport
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA
      ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    (K : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 K]
    (hK : HasProperSupport B (Spec (.of A)) hA X.2 (isAlgebraicSpace_yoneda B _ hA _)
      ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft ((SheafOfModules.toSheaf _).obj K)) :
    Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) K) := by
  have hqc : K.IsQuasicoherentOnSite :=
    (inferInstance : IsCoherent _ _ _ _ _ K).toIsQuasicoherentOnSite
  have hKft : SheafOfModules.IsFiniteTypeOnSite K :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType K inferInstance
  obtain ⟨Zc, G, hGqc, -, hZp, ⟨e⟩⟩ := ((hasProperSupport_tfae B (Spec (.of A)) hA X
    (schemeSpace (baseObject A B hA)) ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft K hqc
    hKft (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _ hKft)).out 1 3).1 hK
  have hGcoh := isCoherent_of_modulePushforward_closedSubspace B (Spec (.of A)) hA X
    (fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft).out K Zc G hGqc e
  have hZp' : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from
      (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).1) := by
    have h : (isTerminal_yoneda_obj_base B _ hA).from
        (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).1 =
        Zc.1.ι ≫ (isTerminal_yoneda_obj_base B _ hA).from X.1 :=
      (isTerminal_yoneda_obj_base B _ hA).hom_ext _ _
    rwa [h]
  have h3 : Function.Bijective (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) ((modulePushforward B (Spec (.of A)) hA
        (closedSubspaceInclusion B (Spec (.of A)) hA X Zc)).obj G)) :=
    bijective_adicSectionsOfSections_closedSubspacePushforward X Zc I G hGqc
      (bijective_adicSectionsOfSections_of_isProper
        (closedSubspaceToSpace B (Spec (.of A)) hA X Zc) hZp' I G)
  exact bijective_adicSectionsOfSections_of_iso.{u, u} B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) e h3

end ProperSupport

/-! ### Stacks 08B9 -/

section FullyFaithful

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A]
  {hA : B.Contains (Spec (.of A))} (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (I : Ideal A) [IsAdicComplete I A]
  (hft : IsFiniteType B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
  (hsep : IsSeparated B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))

include hsep in
/-- **Stacks 08B9.**  In Situation 08B7 — `A` a Noetherian ring complete with respect to an ideal
`I`, `X` an algebraic space separated and of finite type over `Spec A`, and `𝓘 = I 𝒪_X` — let
`M`, `N` be coherent `𝒪_X`-modules such that `Supp M ∩ Supp N` is proper over `Spec A`.  Then the
completion functor of Stacks 08B4 is bijective on `Hom(M, N)`:

`Mor_{Coh(𝒪_X)}(M, N) ⟶ Mor_{Coh(X, 𝓘)}(M^∧, N^∧)`.

The source's proof: by Stacks 08B6 the target is `limₙ H⁰(X, 𝓗 / 𝓘ⁿ 𝓗)` for
`𝓗 = 𝓗om(M, N)`
(`AlgebraicGeometry.Space.bijective_completionFunctor_map_of_bijective_adicSectionsOfSections`);
`𝓗` is coherent with support inside `Supp M ∩ Supp N`, hence proper over `Spec A`
(`AlgebraicGeometry.Space.hasProperSupport_smallEtaleInternalHomSmall`); and the theorem on formal
functions in degree zero for a coherent module with proper support identifies that limit with
`H⁰(X, 𝓗) = Hom(M, N)`
(`AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_hasProperSupport`,
read on the universe lift of `𝓗` by
`AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_moduleULift_iso`). -/
theorem bijective_completionFunctor_map_of_isProperOver_inter
    (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hcl : IsClosed (supportOfSheaf B _ hA X.1 ((SheafOfModules.toSheaf _).obj M.obj) ∩
      supportOfSheaf B _ hA X.1 ((SheafOfModules.toSheaf _).obj N.obj)))
    (hMN : IsProperOver B (Spec (.of A)) hA X.2 (isAlgebraicSpace_yoneda B _ hA _)
      ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1 _ hcl) :
    letI := fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft.1
    Function.Bijective (fun a : M ⟶ N => (completionFunctor B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) (isQuasicoherentOnSite_baseIdealSheaf A X I)).map a) := by
  let := fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft.1
  have hFN := isNoetherian_of_isFiniteType_of_isSeparated_toBase X hft hsep
  refine bijective_completionFunctor_map_of_bijective_adicSectionsOfSections B (Spec (.of A)) hA X
    _ B.contains_terminal hFN _ M N ?_
  have : IsCoherent B (Spec (.of A)) hA X.1 X.2 M.obj := M.property
  have : IsCoherent B (Spec (.of A)) hA X.1 X.2 N.obj := N.property
  have := isCoherent_smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 M.obj N.obj
  have hH := hasProperSupport_smallEtaleInternalHomSmall B (Spec (.of A)) hA X
    (isAlgebraicSpace_yoneda B _ hA _) _ hft.1 M.obj N.obj hcl hMN
  exact bijective_adicSectionsOfSections_of_moduleULift_iso B (Spec (.of A)) hA X.1 X.2 _ _ _
    (smallEtaleInternalHomSmallIso B (Spec (.of A)) hA X.1 X.2 M.obj N.obj)
    (bijective_adicSectionsOfSections_of_hasProperSupport X I hft.1 _ hH)

include hsep in
/-- **Stacks 08B9, with the support condition on the target alone**: if the support of `N` is
proper over `Spec A`, so is `Supp M ∩ Supp N`, and the completion functor is bijective on
`Hom(M, N)`. -/
theorem bijective_completionFunctor_map_of_hasProperSupport
    (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hN : HasProperSupport B (Spec (.of A)) hA X.2 (isAlgebraicSpace_yoneda B _ hA _)
      ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1
      ((SheafOfModules.toSheaf _).obj N.obj)) :
    letI := fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft.1
    Function.Bijective (fun a : M ⟶ N => (completionFunctor B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) (isQuasicoherentOnSite_baseIdealSheaf A X I)).map a) := by
  have : IsCoherent B (Spec (.of A)) hA X.1 X.2 M.obj := M.property
  have hMft : SheafOfModules.IsFiniteTypeOnSite M.obj :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType M.obj inferInstance
  obtain ⟨hNcl, hNp⟩ := hN
  have hcl := (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B _ hA X.1 X.2 M.obj).inter hNcl
  exact bijective_completionFunctor_map_of_isProperOver_inter X I hft hsep M N hcl
    (isProperOver_of_subset B _ hA X.2 _ _ hft.1 _ _ hcl hNcl Set.inter_subset_right hNp)

include hsep in
/-- **Stacks 08B9, "in particular"**: the completion functor
`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, 𝓘)` of equation 76.42.5.1
(Stacks 08B8) is fully faithful. -/
noncomputable def completionFunctorProperOverToBaseFullyFaithful :
    letI := fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 _ X.2 (isAlgebraicSpace_yoneda B _ hA _)
      ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1 (baseIdealSheaf A X I)
      (isQuasicoherentOnSite_baseIdealSheaf A X I)).FullyFaithful := by
  letI := fact_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase X hft.1
  have hb := fun (M N : CoherentModulesProperOver B (Spec (.of A)) hA X.2
      (isAlgebraicSpace_yoneda B _ hA _) ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1) =>
    bijective_completionFunctor_map_of_hasProperSupport X I hft hsep M.obj N.obj N.property
  haveI : (completionFunctorProperOver B (Spec (.of A)) hA X.1 _ X.2
      (isAlgebraicSpace_yoneda B _ hA _) ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1
      (baseIdealSheaf A X I) (isQuasicoherentOnSite_baseIdealSheaf A X I)).Faithful :=
    ⟨fun {M N} a b hab => InducedCategory.hom_ext ((hb M N).1 (congrArg (fun k => k.hom) hab))⟩
  haveI : (completionFunctorProperOver B (Spec (.of A)) hA X.1 _ X.2
      (isAlgebraicSpace_yoneda B _ hA _) ((isTerminal_yoneda_obj_base B _ hA).from X.1) hft.1
      (baseIdealSheaf A X I) (isQuasicoherentOnSite_baseIdealSheaf A X I)).Full :=
    ⟨fun {M N} g => by
      obtain ⟨a, ha⟩ := (hb M N).2 g.hom
      exact ⟨ObjectProperty.homMk a, InducedCategory.hom_ext ha⟩⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

end FullyFaithful

end AlgebraicGeometry.Space

end
