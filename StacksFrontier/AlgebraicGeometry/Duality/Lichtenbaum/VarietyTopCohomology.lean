module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.RestrictedDualVanishing
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpacesCoefficientUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherent cohomology of a variety in degree `dim`

[Stacks, Tag 0G5E]: let `U` be a variety over a field `k` and let `F` be a coherent
`𝒪_U`-module. If `H^d(U, F)` is nonzero, then `dim(U) ≥ d`, and if equality holds, then `U` is
proper over `k`.

## Main results

* `Stacks.Duality.Lichtenbaum.le_topologicalKrullDim_and_isProper_of_not_isZero_rightDerived`:
  **[Stacks, Tag 0G5E]**.
* `Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_nonempty_compl`: `H^d(V, F) = 0` for a
  coherent `F` on an open `V ≠ X` of a proper variety `X` of dimension `d`, by
  [Stacks, Tag 0G5A].
* `Stacks.Duality.Lichtenbaum.le_topologicalKrullDim_of_not_isZero_rightDerived`: the bound
  `d ≤ dim U`, Grothendieck's vanishing theorem ([Stacks, Tag 02UZ]).
* `Stacks.Duality.Lichtenbaum.exists_isIntegral_isProper_isOpenImmersion`: a variety is an open
  subscheme of an integral scheme proper over `k` ([Stacks, Tag 0F41], [Stacks, Tag 0A9Z]).
* `Stacks.Duality.Lichtenbaum.topologicalKrullDim_eq_of_isOpenImmersion`,
  `Stacks.Duality.Lichtenbaum.nonempty_compl_opensRange_of_not_isProper` and
  `Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_subsingleton_dual`: the remaining steps.

## Implementation notes

`H^d(U, F)` is the right derived functor of global sections on `Mod(𝒪_U)`, with values in
`Γ(U, 𝒪_U)`-modules; it is compared with the hypercohomology `H^d(U, F[0])` of
[Stacks, Tag 0G5A] through `Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology` at the
standard model, at which `AlgebraicGeometry.compactSupportDualityLinearEquiv` is stated. The
source replaces the compactification `X` by its reduction; here `X` is the scheme-theoretic
closure of `U` in a Nagata compactification, which is integral, and `U` is carried to the open
subscheme `j(U) ⊆ X` along `j.isoOpensRange`, cohomology being transported by
[Stacks, Tag 089W] for the isomorphism.

## References

* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0A9Z](https://stacks.math.columbia.edu/tag/0A9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality.Lichtenbaum

open _root_.AlgebraicGeometry

/-- **Grothendieck's bound** ([Stacks, Tag 02UZ]): on a nonempty Noetherian scheme `X`, if
`H^d(X, F) ≠ 0` for an `𝒪_X`-module `F` then `d ≤ dim X`. -/
theorem le_topologicalKrullDim_of_not_isZero_rightDerived {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian X] [Nonempty X] (F : X.Modules) (d : ℕ)
    (h : ¬ IsZero (((moduleGlobalSections X).rightDerived d).obj F)) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  by_contra! hlt
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim X = e := by
    have hbot : topologicalKrullDim X ≠ ⊥ := fun hb =>
      not_isEmpty_of_nonempty X ((topologicalKrullDim_eq_bot_iff_isEmpty X).mp hb)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hatop : a ≠ ⊤ := by
      intro ha'
      rw [← ha, ha'] at hlt
      exact (not_lt_of_ge le_top) hlt
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hatop
    exact ⟨e, ha.symm.trans (congrArg WithBot.some he.symm)⟩
  have hed : e < d := by
    rw [he] at hlt
    exact_mod_cast hlt
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  exact h <| (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf ⊤ d F).2
    ((Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH X d F).2
      (CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le_of_coefficients
        (X := X) he.le hed _))

/-- **An integral compactification of a variety** ([Stacks, Tag 0F41] and [Stacks, Tag 0A9Z]): a
variety `U` over `k` is an open subscheme of an integral scheme proper over `k`. Nagata's theorem
gives a compactification `U ⟶ X̄` over `k`; the scheme-theoretic image of `U` in `X̄` is reduced
and irreducible, hence integral, closed in `X̄`, hence proper over `k`, and contains `U` as an open
subscheme. This replaces "replacing `X` by its reduction" in the source by the scheme-theoretic
closure of `U`, which is the same thing when `U` is dense. -/
theorem exists_isIntegral_isProper_isOpenImmersion (k : Type u) [Field k] {U : Scheme.{u}}
    (f : U ⟶ Spec (.of k)) [IsVariety k f] :
    ∃ (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) (_ : IsProper q) (_ : IsIntegral X) (j : U ⟶ X)
      (_ : IsOpenImmersion j), j ≫ q = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  let i := c.immersion
  have : IsOpenImmersion i.toImage := isOpenImmersion_toImage i (.inl hc)
  have : IrreducibleSpace i.image := by
    refine (irreducibleSpace_def _).mpr ?_
    rw [Set.top_eq_univ, ← i.toImage.denseRange.closure_range, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ U).image _
      i.toImage.continuous.continuousOn).closure
  have : IsIntegral i.image := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨i.image, i.imageι ≫ c.toBase, inferInstance, inferInstance, i.toImage, inferInstance, ?_⟩
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact Over.w c.obj.hom

/-- A nonempty open subscheme of an irreducible scheme locally of finite type over a field has
the dimension of the ambient scheme ([Stacks, Tag 0A21]). -/
@[sga "3 VIB 1.5" "more general"]
theorem topologicalKrullDim_eq_of_isOpenImmersion (k : Type u) [Field k] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    [IrreducibleSpace X] [Nonempty U] :
    topologicalKrullDim X = topologicalKrullDim U :=
  (topologicalKrullDim_eq_of_isOpen k X q (Set.range j) j.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _)).trans
      (IsHomeomorph.topologicalKrullDim_eq _
        j.isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- If an open immersion `j : U ⟶ X` into a scheme proper over `S` is surjective, then `U` is
proper over `S`; so a non-proper `U` misses a point of `X`. -/
theorem nonempty_compl_opensRange_of_not_isProper {U X S : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (q : X ⟶ S) [IsProper q] (hf : ¬ IsProper (j ≫ q)) :
    ((j.opensRange : Set X)ᶜ).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  have : Surjective j := ⟨fun x => (h ▸ Set.mem_univ x : x ∈ (j.opensRange : Set X))⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨inferInstance, inferInstance⟩
  exact hf inferInstance

/-- **Vanishing from the vanishing of the dual.** `H^n(X, F)`, as a vector space over `k`, is
zero as soon as its `k`-dual is. -/
theorem isZero_rightDerived_of_subsingleton_dual (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ)
    (h : Subsingleton (cohomologyOverField k f F n →ₗ[k] k)) :
    IsZero (((moduleGlobalSections X).rightDerived n).obj F) := by
  have hs : Subsingleton (cohomologyOverField k f F n) := subsingleton_of_forall_eq 0 fun v =>
    (Module.forall_dual_apply_eq_zero_iff k v).1 fun φ => by
      rw [Subsingleton.elim φ 0]
      rfl
  rw [ModuleCat.isZero_iff_subsingleton]
  exact hs

/-- **`H^d(V, F) = 0` for a coherent `F` on a non-proper open `V` of a proper variety of dimension
`d`.** By the duality of [Stacks, Tag 0G5A] (`AlgebraicGeometry.compactSupportDualityLinearEquiv`,
at the compactification `V ⊆ X`), the `k`-dual of `H^d(V, F)` is
`H^{-d}_c(V, R𝓗om(F, ω_V^•))`, which vanishes
(`Stacks.Duality.Lichtenbaum.subsingleton_compactSupportCohomology_of_iso_derivedDualInto`). -/
theorem isZero_rightDerived_of_nonempty_compl (k : Type u) [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsProper q] [IsIntegral X] (d : ℕ) (hd : topologicalKrullDim X = d)
    (V : X.Opens) (hV : ((V : Set X)ᶜ).Nonempty) (F : V.toScheme.Modules) [hF : F.IsCoherent] :
    IsZero (((moduleGlobalSections V.toScheme).rightDerived d).obj F) := by
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : _root_.AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ q)
  let := HasDerivedCategory.standard V.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} k)
  let K : BoundedCoherentDerived V :=
    ⟨(DerivedCategory.singleFunctor V.toScheme.Modules 0).obj F,
      derivedCategoryBBounded_singleFunctor_obj V F hF⟩
  have hsub := subsingleton_compactSupportCohomology_of_iso_derivedDualInto q d hd V hV F hF
    (openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ q)
      (_root_.AlgebraicGeometry.openCompactification q V))
      (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ q)
        (_root_.AlgebraicGeometry.openCompactification q V)) K) ⟨Iso.refl _⟩
  let e : cohomologyOverFieldFunctor k (V.ι ≫ q) d ≅ _ :=
    rightDerivedCompRestrictScalarsIso
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (V.ι ≫ q).appLE ⊤ ⊤ (by simp)).hom
        (_root_.SheafOfModules.evaluation V.toScheme.ringCatSheaf (op (⊤ : V.toScheme.Opens)))
        (globalSectionsOver (V.ι ≫ q)) (evaluationCompRestrictScalarsIsoGlobalSectionsOver k _) d
        (hE := AlgebraicGeometry.evaluationAdditive V.toScheme)
        (hH := AlgebraicGeometry.globalSectionsOver_additive _) ≪≫
      rightDerivedGlobalSectionsIsoDerivedCohomology (V.ι ≫ q) d
  have : Subsingleton (Module.Dual k ((DerivedCategory.singleFunctor V.toScheme.Modules 0 ⋙
      derivedGlobalSectionsOver (V.ι ≫ q) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) (d : ℤ)).obj F)) :=
    (compactSupportDualityLinearEquiv (V.ι ≫ q)
      (_root_.AlgebraicGeometry.openCompactification q V) K (d : ℤ)).toEquiv.subsingleton
  exact isZero_rightDerived_of_subsingleton_dual k (V.ι ≫ q) F d
    (e.app F).toLinearEquiv.dualMap.symm.toEquiv.subsingleton

/-- **[Stacks, Tag 0G5E].** Let `U` be a variety over a field `k` and let `F` be a coherent
`𝒪_U`-module. If `H^d(U, F)` is nonzero, then `dim(U) ≥ d`, and if equality holds, then `U` is
proper over `k`.

Here `H^d(U, F)` is the `d`-th right derived functor of global sections on `Mod(𝒪_U)`, and
`dim(U)` is the topological Krull dimension. The proof is the source's. The bound is
Grothendieck's vanishing theorem ([Stacks, Tag 02UZ]). If `dim U = d`, choose an integral scheme
`X` proper over `k` containing `U` as an open subscheme ([Stacks, Tag 0F41],
[Stacks, Tag 0A9Z]); then `dim X = d`, and if `U` is not proper then `U ≠ X`, so
`H^d(U, F) = 0` by duality ([Stacks, Tag 0G5A]) and the vanishing of
`H^{-d}_c(U, R𝓗om(F, ω_U^•))`
(`Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_nonempty_compl`). -/
@[stacks 0G5E]
theorem le_topologicalKrullDim_and_isProper_of_not_isZero_rightDerived (k : Type u) [Field k]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) [IsVariety k f] (F : U.Modules) [F.IsCoherent]
    (d : ℕ) (h : ¬ IsZero (((moduleGlobalSections U).rightDerived d).obj F)) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim U ∧ (topologicalKrullDim U = d → IsProper f) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace f
  have : _root_.AlgebraicGeometry.IsNoetherian U := ⟨⟩
  refine ⟨le_topologicalKrullDim_of_not_isZero_rightDerived F d h, fun hdim => ?_⟩
  by_contra hf
  obtain ⟨X, q, _, _, j, _, hjq⟩ := exists_isIntegral_isProper_isOpenImmersion k f
  have hdX : topologicalKrullDim X = d :=
    (topologicalKrullDim_eq_of_isOpenImmersion k j q).trans hdim
  have hV := nonempty_compl_opensRange_of_not_isProper j q (hjq ▸ hf)
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let F' := (Scheme.Modules.pushforward j.isoOpensRange.hom).obj F
  have : F'.IsCoherent :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite _ F
  apply h
  have hR := (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
    j.isoOpensRange.hom F d).isZero_iff.2
      (isZero_rightDerived_of_nonempty_compl k q d hdX j.opensRange hV F')
  rw [ModuleCat.isZero_iff_subsingleton] at hR ⊢
  assumption

end Stacks.Duality.Lichtenbaum

end
